use axia::{
    ast::{Formula, Sort, Term},
    engine::{forward_deduce, prove, Axiom, Universe},
};
use criterion::{black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};

fn predicate(name: impl Into<String>, term: Term) -> Formula {
    Formula::Pred(name.into(), vec![term])
}

fn build_workload(chain_length: usize) -> Universe {
    let mut universe = Universe::new();
    universe.add_constant("a".into(), Sort::object());

    // A useful chain: P0(a) -> P1(a) -> ... -> Pn(a).
    for index in 0..=chain_length {
        universe.add_predicate(
            format!("P{index}"),
            vec!["Object".into()],
            "Prop".into(),
        );
    }

    for index in 0..chain_length {
        let variable = Term::Var("x".into(), Sort::object());
        universe.add_axiom(Axiom {
            name: format!("P{index}_to_P{}", index + 1),
            vars: vec!["x".into()],
            premises: vec![predicate(format!("P{index}"), variable.clone())],
            conclusion: predicate(format!("P{}", index + 1), variable),
        });
    }

    universe.add_given(
        "start".into(),
        predicate("P0", Term::Const("a".into())),
    );

    // Distractor facts and rules make the indexes do real filtering work.
    // None of these predicates can contribute to the P-chain proof.
    for index in 0..chain_length {
        let source = format!("Noise{index}");
        let target = format!("NoiseNext{index}");
        universe.add_predicate(
            source.clone(),
            vec!["Object".into()],
            "Prop".into(),
        );
        universe.add_predicate(
            target.clone(),
            vec!["Object".into()],
            "Prop".into(),
        );
        universe.add_given(
            format!("noise_fact_{index}"),
            predicate(source.clone(), Term::Const("a".into())),
        );

        let variable = Term::Var("noise_x".into(), Sort::object());
        universe.add_axiom(Axiom {
            name: format!("irrelevant_rule_{index}"),
            vars: vec!["noise_x".into()],
            premises: vec![predicate(source, variable.clone())],
            conclusion: predicate(target, variable),
        });
    }

    universe
}

fn build_rewrite_workload(size: usize) -> Universe {
    let mut universe = Universe::new();
    let x = Term::Var("x".into(), Sort::object());
    let wrapped = |term: Term| Term::Apply("Wrap".into(), vec![term]);

    universe.add_axiom(Axiom {
        name: "unwrap".into(),
        vars: vec!["x".into()],
        premises: vec![],
        conclusion: Formula::Eq(wrapped(x.clone()), x.clone()),
    });

    for index in 0..size {
        let noise = Term::Var(format!("noise_{index}").into(), Sort::object());
        universe.add_axiom(Axiom {
            name: format!("irrelevant_rewrite_{index}"),
            vars: vec![format!("noise_{index}").into()],
            premises: vec![],
            conclusion: Formula::Eq(
                Term::Apply(format!("Noise{index}"), vec![noise.clone()]),
                noise,
            ),
        });
    }

    for index in 0..size {
        let variable = Term::Var("value".into(), Sort::object());
        universe.add_axiom(Axiom {
            name: format!("P{index}_to_P{}", index + 1),
            vars: vec!["value".into()],
            premises: vec![predicate(format!("P{index}"), variable.clone())],
            conclusion: predicate(format!("P{}", index + 1), variable),
        });
    }

    universe.add_given(
        "start".into(),
        predicate("P0", wrapped(Term::Const("a".into()))),
    );
    universe
}

fn benchmark_forward_rewrite_index(c: &mut Criterion) {
    let mut group = c.benchmark_group("forward_deduction_with_rewrite_distractors");
    for size in [8usize, 32, 128] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || build_rewrite_workload(size),
                |mut universe| {
                    black_box(forward_deduce(&mut universe, (size + 2) as u32));
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

fn benchmark_proof_search(c: &mut Criterion) {
    let mut group = c.benchmark_group("proof_search_with_distractors");
    for size in [8usize, 32, 128] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || build_workload(size),
                |universe| {
                    let goal = predicate(
                        format!("P{size}"),
                        Term::Const("a".into()),
                    );
                    black_box(prove(&goal, &universe, (size + 2) as u32));
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

fn benchmark_forward_deduction(c: &mut Criterion) {
    let mut group = c.benchmark_group("forward_deduction_with_distractors");
    for size in [8usize, 32, 128] {
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || build_workload(size),
                |mut universe| {
                    black_box(forward_deduce(
                        &mut universe,
                        (size + 2) as u32,
                    ));
                },
                BatchSize::SmallInput,
            );
        });
    }
    group.finish();
}

criterion_group!(
    engine_benches,
    benchmark_proof_search,
    benchmark_forward_deduction,
    benchmark_forward_rewrite_index
);
criterion_main!(engine_benches);
