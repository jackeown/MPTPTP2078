%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0762+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:04 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 169 expanded)
%              Number of clauses        :   45 (  45 expanded)
%              Number of leaves         :    9 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  417 ( 940 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ~ r1_relat_2(X0,k3_relat_1(X0)) )
        & ( r1_relat_2(X0,k3_relat_1(X0))
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ~ r1_wellord1(X0,k3_relat_1(X0)) )
        & ( r1_wellord1(X0,k3_relat_1(X0))
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ r8_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ~ r6_relat_2(X0,k3_relat_1(X0)) )
        & ( r6_relat_2(X0,k3_relat_1(X0))
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ r6_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ r4_relat_2(X0,k3_relat_1(X0)) )
        & ( r4_relat_2(X0,k3_relat_1(X0))
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ r4_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_wellord1(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X0] :
      ( r4_relat_2(X0,k3_relat_1(X0))
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_wellord1(X0,X1)
      | ~ r1_wellord1(X0,X1)
      | ~ r6_relat_2(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0] :
      ( r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X0] :
      ( r8_relat_2(X0,k3_relat_1(X0))
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0] :
      ( r6_relat_2(X0,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( r2_wellord1(X0,k3_relat_1(X0))
        <=> v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <~> v2_wellord1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ? [X0] :
      ( ( ~ v2_wellord1(X0)
        | ~ r2_wellord1(X0,k3_relat_1(X0)) )
      & ( v2_wellord1(X0)
        | r2_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f28,plain,(
    ? [X0] :
      ( ( ~ v2_wellord1(X0)
        | ~ r2_wellord1(X0,k3_relat_1(X0)) )
      & ( v2_wellord1(X0)
        | r2_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,
    ( ? [X0] :
        ( ( ~ v2_wellord1(X0)
          | ~ r2_wellord1(X0,k3_relat_1(X0)) )
        & ( v2_wellord1(X0)
          | r2_wellord1(X0,k3_relat_1(X0)) )
        & v1_relat_1(X0) )
   => ( ( ~ v2_wellord1(sK0)
        | ~ r2_wellord1(sK0,k3_relat_1(sK0)) )
      & ( v2_wellord1(sK0)
        | r2_wellord1(sK0,k3_relat_1(sK0)) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ~ v2_wellord1(sK0)
      | ~ r2_wellord1(sK0,k3_relat_1(sK0)) )
    & ( v2_wellord1(sK0)
      | r2_wellord1(sK0,k3_relat_1(sK0)) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f55,plain,
    ( ~ v2_wellord1(sK0)
    | ~ r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,
    ( v2_wellord1(sK0)
    | r2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_18,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | v1_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,plain,
    ( ~ r1_wellord1(X0,k3_relat_1(X0))
    | v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4,plain,
    ( ~ r8_relat_2(X0,k3_relat_1(X0))
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( ~ r6_relat_2(X0,k3_relat_1(X0))
    | v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( ~ r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v4_relat_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( ~ v1_relat_2(X0)
    | ~ v1_wellord1(X0)
    | v2_wellord1(X0)
    | ~ v8_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | ~ v4_relat_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_332,plain,
    ( ~ r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_2(X0)
    | ~ v1_wellord1(X0)
    | v2_wellord1(X0)
    | ~ v8_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_0,c_6])).

cnf(c_386,plain,
    ( ~ r6_relat_2(X0,k3_relat_1(X0))
    | ~ r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_2(X0)
    | ~ v1_wellord1(X0)
    | v2_wellord1(X0)
    | ~ v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_2,c_332])).

cnf(c_440,plain,
    ( ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ r6_relat_2(X0,k3_relat_1(X0))
    | ~ r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_2(X0)
    | ~ v1_wellord1(X0)
    | v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4,c_386])).

cnf(c_479,plain,
    ( ~ r1_wellord1(X0,k3_relat_1(X0))
    | ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ r6_relat_2(X0,k3_relat_1(X0))
    | ~ r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_2(X0)
    | v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_440])).

cnf(c_533,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | ~ r1_wellord1(X0,k3_relat_1(X0))
    | ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ r6_relat_2(X0,k3_relat_1(X0))
    | ~ r4_relat_2(X0,k3_relat_1(X0))
    | v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_479])).

cnf(c_15,plain,
    ( ~ r2_wellord1(X0,X1)
    | r4_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_609,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | ~ r1_wellord1(X0,k3_relat_1(X0))
    | ~ r2_wellord1(X0,k3_relat_1(X0))
    | ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ r6_relat_2(X0,k3_relat_1(X0))
    | v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_533,c_15])).

cnf(c_14,plain,
    ( ~ r2_wellord1(X0,X1)
    | r6_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,plain,
    ( ~ r2_wellord1(X0,X1)
    | r8_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,plain,
    ( r1_wellord1(X0,X1)
    | ~ r2_wellord1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,plain,
    ( r1_relat_2(X0,X1)
    | ~ r2_wellord1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_627,plain,
    ( ~ r2_wellord1(X0,k3_relat_1(X0))
    | v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_609,c_14,c_16,c_13,c_17])).

cnf(c_632,plain,
    ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
    | v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_9,plain,
    ( ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0)
    | v4_relat_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v4_relat_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_318,plain,
    ( r4_relat_2(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_9,c_1])).

cnf(c_12,plain,
    ( ~ r1_relat_2(X0,X1)
    | ~ r1_wellord1(X0,X1)
    | r2_wellord1(X0,X1)
    | ~ r8_relat_2(X0,X1)
    | ~ r6_relat_2(X0,X1)
    | ~ r4_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_589,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | ~ r1_wellord1(X0,k3_relat_1(X0))
    | r2_wellord1(X0,k3_relat_1(X0))
    | ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ r6_relat_2(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_318,c_12])).

cnf(c_591,plain,
    ( ~ r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_11,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19,plain,
    ( r1_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_561,plain,
    ( r1_relat_2(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_19])).

cnf(c_563,plain,
    ( r1_relat_2(sK0,k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_7,plain,
    ( v1_wellord1(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_21,plain,
    ( r1_wellord1(X0,k3_relat_1(X0))
    | ~ v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_507,plain,
    ( r1_wellord1(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_7,c_21])).

cnf(c_509,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_10,plain,
    ( ~ v2_wellord1(X0)
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5,plain,
    ( r8_relat_2(X0,k3_relat_1(X0))
    | ~ v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_426,plain,
    ( r8_relat_2(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_5])).

cnf(c_428,plain,
    ( r8_relat_2(sK0,k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_426])).

cnf(c_8,plain,
    ( ~ v2_wellord1(X0)
    | v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( r6_relat_2(X0,k3_relat_1(X0))
    | ~ v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_372,plain,
    ( r6_relat_2(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_8,c_3])).

cnf(c_374,plain,
    ( r6_relat_2(sK0,k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_22,negated_conjecture,
    ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( r2_wellord1(sK0,k3_relat_1(sK0))
    | v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_632,c_591,c_563,c_509,c_428,c_374,c_22,c_23,c_24])).


%------------------------------------------------------------------------------
