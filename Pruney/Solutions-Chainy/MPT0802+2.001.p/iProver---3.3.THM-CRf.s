%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:35 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 312 expanded)
%              Number of clauses        :   55 (  66 expanded)
%              Number of leaves         :   12 (  88 expanded)
%              Depth                    :   12
%              Number of atoms          :  530 (2079 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ~ r1_relat_2(X0,k3_relat_1(X0)) )
        & ( r1_relat_2(X0,k3_relat_1(X0))
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0] :
      ( r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ~ r1_wellord1(X0,k3_relat_1(X0)) )
        & ( r1_wellord1(X0,k3_relat_1(X0))
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0] :
      ( r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( r8_relat_2(X0,k3_relat_1(X0))
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ~ r6_relat_2(X0,k3_relat_1(X0)) )
        & ( r6_relat_2(X0,k3_relat_1(X0))
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( r6_relat_2(X0,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ r4_relat_2(X0,k3_relat_1(X0)) )
        & ( r4_relat_2(X0,k3_relat_1(X0))
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( r4_relat_2(X0,k3_relat_1(X0))
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_wellord1(X0,X1)
      | ~ r1_wellord1(X0,X1)
      | ~ r6_relat_2(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ( ( v1_wellord1(X0)
                   => v1_wellord1(X1) )
                  & ( v4_relat_2(X0)
                   => v4_relat_2(X1) )
                  & ( v6_relat_2(X0)
                   => v6_relat_2(X1) )
                  & ( v8_relat_2(X0)
                   => v8_relat_2(X1) )
                  & ( v1_relat_2(X0)
                   => v1_relat_2(X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_2(X1)
      | ~ v4_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => v2_wellord1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( r3_wellord1(X0,X1,X2)
                    & v2_wellord1(X0) )
                 => v2_wellord1(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_wellord1(X1)
          & r3_wellord1(X0,X1,X2)
          & v2_wellord1(X0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ~ v2_wellord1(X1)
        & r3_wellord1(X0,X1,sK2)
        & v2_wellord1(X0)
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ v2_wellord1(sK1)
            & r3_wellord1(X0,sK1,X2)
            & v2_wellord1(X0)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_wellord1(X1)
                & r3_wellord1(X0,X1,X2)
                & v2_wellord1(X0)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(sK0,X1,X2)
              & v2_wellord1(sK0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ v2_wellord1(sK1)
    & r3_wellord1(sK0,sK1,sK2)
    & v2_wellord1(sK0)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f32,f31,f30])).

fof(f62,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( r2_wellord1(X0,k3_relat_1(X0))
          | ~ v2_wellord1(X0) )
        & ( v2_wellord1(X0)
          | ~ r2_wellord1(X0,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X0] :
      ( r2_wellord1(X0,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ r4_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_wellord1(X1)
      | ~ v1_wellord1(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v6_relat_2(X1)
      | ~ v6_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v8_relat_2(X1)
      | ~ v8_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_2(X1)
      | ~ v1_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_wellord1(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ r1_wellord1(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ r8_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r8_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ r6_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r6_relat_2(X0,X1)
      | ~ r2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ r2_wellord1(X0,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ~ v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,plain,
    ( r1_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,plain,
    ( r1_wellord1(X0,k3_relat_1(X0))
    | ~ v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5,plain,
    ( r8_relat_2(X0,k3_relat_1(X0))
    | ~ v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( r6_relat_2(X0,k3_relat_1(X0))
    | ~ v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v4_relat_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( ~ r1_relat_2(X0,X1)
    | ~ r1_wellord1(X0,X1)
    | r2_wellord1(X0,X1)
    | ~ r8_relat_2(X0,X1)
    | ~ r6_relat_2(X0,X1)
    | ~ r4_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_331,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | ~ r1_wellord1(X0,k3_relat_1(X0))
    | r2_wellord1(X0,k3_relat_1(X0))
    | ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ r6_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v4_relat_2(X0) ),
    inference(resolution,[status(thm)],[c_1,c_6])).

cnf(c_381,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | ~ r1_wellord1(X0,k3_relat_1(X0))
    | r2_wellord1(X0,k3_relat_1(X0))
    | ~ r8_relat_2(X0,k3_relat_1(X0))
    | ~ v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | ~ v4_relat_2(X0) ),
    inference(resolution,[status(thm)],[c_3,c_331])).

cnf(c_433,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | ~ r1_wellord1(X0,k3_relat_1(X0))
    | r2_wellord1(X0,k3_relat_1(X0))
    | ~ v8_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | ~ v4_relat_2(X0) ),
    inference(resolution,[status(thm)],[c_5,c_381])).

cnf(c_485,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | r2_wellord1(X0,k3_relat_1(X0))
    | ~ v1_wellord1(X0)
    | ~ v8_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | ~ v4_relat_2(X0) ),
    inference(resolution,[status(thm)],[c_20,c_433])).

cnf(c_537,plain,
    ( r2_wellord1(X0,k3_relat_1(X0))
    | ~ v1_wellord1(X0)
    | ~ v1_relat_2(X0)
    | ~ v8_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | ~ v4_relat_2(X0) ),
    inference(resolution,[status(thm)],[c_13,c_485])).

cnf(c_15,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_2(X0)
    | v4_relat_2(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,negated_conjecture,
    ( r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_619,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v4_relat_2(sK0)
    | v4_relat_2(sK1) ),
    inference(resolution,[status(thm)],[c_15,c_24])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,plain,
    ( r2_wellord1(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_39,plain,
    ( r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_0,plain,
    ( ~ r4_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v4_relat_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,plain,
    ( ~ r2_wellord1(X0,X1)
    | r4_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_355,plain,
    ( ~ r2_wellord1(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v4_relat_2(X0) ),
    inference(resolution,[status(thm)],[c_0,c_9])).

cnf(c_357,plain,
    ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | v4_relat_2(sK0) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_621,plain,
    ( v4_relat_2(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_29,c_28,c_27,c_26,c_25,c_39,c_357])).

cnf(c_650,plain,
    ( r2_wellord1(sK1,k3_relat_1(sK1))
    | ~ v1_wellord1(sK1)
    | ~ v1_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | ~ v6_relat_2(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_537,c_621])).

cnf(c_14,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_wellord1(X0)
    | v1_wellord1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_629,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_wellord1(sK0)
    | v1_wellord1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_14,c_24])).

cnf(c_16,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v6_relat_2(X0)
    | v6_relat_2(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_609,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v6_relat_2(sK0)
    | v6_relat_2(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_16,c_24])).

cnf(c_17,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v8_relat_2(X0)
    | v8_relat_2(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_599,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v8_relat_2(sK0)
    | v8_relat_2(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_17,c_24])).

cnf(c_18,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_2(X0)
    | v1_relat_2(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_589,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_2(sK0)
    | v1_relat_2(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_18,c_24])).

cnf(c_11,plain,
    ( r1_relat_2(X0,X1)
    | ~ r2_wellord1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,plain,
    ( ~ r1_relat_2(X0,k3_relat_1(X0))
    | v1_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_563,plain,
    ( ~ r2_wellord1(X0,k3_relat_1(X0))
    | v1_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_12])).

cnf(c_565,plain,
    ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
    | v1_relat_2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_7,plain,
    ( r1_wellord1(X0,X1)
    | ~ r2_wellord1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,plain,
    ( ~ r1_wellord1(X0,k3_relat_1(X0))
    | v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_511,plain,
    ( ~ r2_wellord1(X0,k3_relat_1(X0))
    | v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_7,c_19])).

cnf(c_513,plain,
    ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
    | v1_wellord1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_4,plain,
    ( ~ r8_relat_2(X0,k3_relat_1(X0))
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_10,plain,
    ( ~ r2_wellord1(X0,X1)
    | r8_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_459,plain,
    ( ~ r2_wellord1(X0,k3_relat_1(X0))
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4,c_10])).

cnf(c_461,plain,
    ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
    | v8_relat_2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_459])).

cnf(c_2,plain,
    ( ~ r6_relat_2(X0,k3_relat_1(X0))
    | v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
    ( ~ r2_wellord1(X0,X1)
    | r6_relat_2(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_407,plain,
    ( ~ r2_wellord1(X0,k3_relat_1(X0))
    | v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_2,c_8])).

cnf(c_409,plain,
    ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
    | v6_relat_2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_22,plain,
    ( ~ r2_wellord1(X0,k3_relat_1(X0))
    | v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( ~ v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_305,plain,
    ( ~ r2_wellord1(sK1,k3_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_22,c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_650,c_629,c_609,c_599,c_589,c_565,c_513,c_461,c_409,c_305,c_39,c_25,c_26,c_27,c_28,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.83/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.83/1.00  
% 0.83/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.83/1.00  
% 0.83/1.00  ------  iProver source info
% 0.83/1.00  
% 0.83/1.00  git: date: 2020-06-30 10:37:57 +0100
% 0.83/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.83/1.00  git: non_committed_changes: false
% 0.83/1.00  git: last_make_outside_of_git: false
% 0.83/1.00  
% 0.83/1.00  ------ 
% 0.83/1.00  
% 0.83/1.00  ------ Input Options
% 0.83/1.00  
% 0.83/1.00  --out_options                           all
% 0.83/1.00  --tptp_safe_out                         true
% 0.83/1.00  --problem_path                          ""
% 0.83/1.00  --include_path                          ""
% 0.83/1.00  --clausifier                            res/vclausify_rel
% 0.83/1.00  --clausifier_options                    --mode clausify
% 0.83/1.00  --stdin                                 false
% 0.83/1.00  --stats_out                             all
% 0.83/1.00  
% 0.83/1.00  ------ General Options
% 0.83/1.00  
% 0.83/1.00  --fof                                   false
% 0.83/1.00  --time_out_real                         305.
% 0.83/1.00  --time_out_virtual                      -1.
% 0.83/1.00  --symbol_type_check                     false
% 0.83/1.00  --clausify_out                          false
% 0.83/1.00  --sig_cnt_out                           false
% 0.83/1.00  --trig_cnt_out                          false
% 0.83/1.00  --trig_cnt_out_tolerance                1.
% 0.83/1.00  --trig_cnt_out_sk_spl                   false
% 0.83/1.00  --abstr_cl_out                          false
% 0.83/1.00  
% 0.83/1.00  ------ Global Options
% 0.83/1.00  
% 0.83/1.00  --schedule                              default
% 0.83/1.00  --add_important_lit                     false
% 0.83/1.00  --prop_solver_per_cl                    1000
% 0.83/1.00  --min_unsat_core                        false
% 0.83/1.00  --soft_assumptions                      false
% 0.83/1.00  --soft_lemma_size                       3
% 0.83/1.00  --prop_impl_unit_size                   0
% 0.83/1.00  --prop_impl_unit                        []
% 0.83/1.00  --share_sel_clauses                     true
% 0.83/1.00  --reset_solvers                         false
% 0.83/1.00  --bc_imp_inh                            [conj_cone]
% 0.83/1.00  --conj_cone_tolerance                   3.
% 0.83/1.00  --extra_neg_conj                        none
% 0.83/1.00  --large_theory_mode                     true
% 0.83/1.00  --prolific_symb_bound                   200
% 0.83/1.00  --lt_threshold                          2000
% 0.83/1.00  --clause_weak_htbl                      true
% 0.83/1.00  --gc_record_bc_elim                     false
% 0.83/1.00  
% 0.83/1.00  ------ Preprocessing Options
% 0.83/1.00  
% 0.83/1.00  --preprocessing_flag                    true
% 0.83/1.00  --time_out_prep_mult                    0.1
% 0.83/1.00  --splitting_mode                        input
% 0.83/1.00  --splitting_grd                         true
% 0.83/1.00  --splitting_cvd                         false
% 0.83/1.00  --splitting_cvd_svl                     false
% 0.83/1.00  --splitting_nvd                         32
% 0.83/1.00  --sub_typing                            true
% 0.83/1.00  --prep_gs_sim                           true
% 0.83/1.00  --prep_unflatten                        true
% 0.83/1.00  --prep_res_sim                          true
% 0.83/1.00  --prep_upred                            true
% 0.83/1.00  --prep_sem_filter                       exhaustive
% 0.83/1.00  --prep_sem_filter_out                   false
% 0.83/1.00  --pred_elim                             true
% 0.83/1.00  --res_sim_input                         true
% 0.83/1.00  --eq_ax_congr_red                       true
% 0.83/1.00  --pure_diseq_elim                       true
% 0.83/1.00  --brand_transform                       false
% 0.83/1.00  --non_eq_to_eq                          false
% 0.83/1.00  --prep_def_merge                        true
% 0.83/1.00  --prep_def_merge_prop_impl              false
% 0.83/1.00  --prep_def_merge_mbd                    true
% 0.83/1.00  --prep_def_merge_tr_red                 false
% 0.83/1.00  --prep_def_merge_tr_cl                  false
% 0.83/1.00  --smt_preprocessing                     true
% 0.83/1.00  --smt_ac_axioms                         fast
% 0.83/1.00  --preprocessed_out                      false
% 0.83/1.00  --preprocessed_stats                    false
% 0.83/1.00  
% 0.83/1.00  ------ Abstraction refinement Options
% 0.83/1.00  
% 0.83/1.00  --abstr_ref                             []
% 0.83/1.00  --abstr_ref_prep                        false
% 0.83/1.00  --abstr_ref_until_sat                   false
% 0.83/1.00  --abstr_ref_sig_restrict                funpre
% 0.83/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/1.00  --abstr_ref_under                       []
% 0.83/1.00  
% 0.83/1.00  ------ SAT Options
% 0.83/1.00  
% 0.83/1.00  --sat_mode                              false
% 0.83/1.00  --sat_fm_restart_options                ""
% 0.83/1.00  --sat_gr_def                            false
% 0.83/1.00  --sat_epr_types                         true
% 0.83/1.00  --sat_non_cyclic_types                  false
% 0.83/1.00  --sat_finite_models                     false
% 0.83/1.00  --sat_fm_lemmas                         false
% 0.83/1.00  --sat_fm_prep                           false
% 0.83/1.00  --sat_fm_uc_incr                        true
% 0.83/1.00  --sat_out_model                         small
% 0.83/1.00  --sat_out_clauses                       false
% 0.83/1.00  
% 0.83/1.00  ------ QBF Options
% 0.83/1.00  
% 0.83/1.00  --qbf_mode                              false
% 0.83/1.00  --qbf_elim_univ                         false
% 0.83/1.00  --qbf_dom_inst                          none
% 0.83/1.00  --qbf_dom_pre_inst                      false
% 0.83/1.00  --qbf_sk_in                             false
% 0.83/1.00  --qbf_pred_elim                         true
% 0.83/1.00  --qbf_split                             512
% 0.83/1.00  
% 0.83/1.00  ------ BMC1 Options
% 0.83/1.00  
% 0.83/1.00  --bmc1_incremental                      false
% 0.83/1.00  --bmc1_axioms                           reachable_all
% 0.83/1.00  --bmc1_min_bound                        0
% 0.83/1.00  --bmc1_max_bound                        -1
% 0.83/1.00  --bmc1_max_bound_default                -1
% 0.83/1.00  --bmc1_symbol_reachability              true
% 0.83/1.00  --bmc1_property_lemmas                  false
% 0.83/1.00  --bmc1_k_induction                      false
% 0.83/1.00  --bmc1_non_equiv_states                 false
% 0.83/1.00  --bmc1_deadlock                         false
% 0.83/1.00  --bmc1_ucm                              false
% 0.83/1.00  --bmc1_add_unsat_core                   none
% 0.83/1.00  --bmc1_unsat_core_children              false
% 0.83/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/1.00  --bmc1_out_stat                         full
% 0.83/1.00  --bmc1_ground_init                      false
% 0.83/1.00  --bmc1_pre_inst_next_state              false
% 0.83/1.00  --bmc1_pre_inst_state                   false
% 0.83/1.00  --bmc1_pre_inst_reach_state             false
% 0.83/1.00  --bmc1_out_unsat_core                   false
% 0.83/1.00  --bmc1_aig_witness_out                  false
% 0.83/1.00  --bmc1_verbose                          false
% 0.83/1.00  --bmc1_dump_clauses_tptp                false
% 0.83/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.83/1.00  --bmc1_dump_file                        -
% 0.83/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.83/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.83/1.00  --bmc1_ucm_extend_mode                  1
% 0.83/1.00  --bmc1_ucm_init_mode                    2
% 0.83/1.00  --bmc1_ucm_cone_mode                    none
% 0.83/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.83/1.00  --bmc1_ucm_relax_model                  4
% 0.83/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.83/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/1.00  --bmc1_ucm_layered_model                none
% 0.83/1.00  --bmc1_ucm_max_lemma_size               10
% 0.83/1.00  
% 0.83/1.00  ------ AIG Options
% 0.83/1.00  
% 0.83/1.00  --aig_mode                              false
% 0.83/1.00  
% 0.83/1.00  ------ Instantiation Options
% 0.83/1.00  
% 0.83/1.00  --instantiation_flag                    true
% 0.83/1.00  --inst_sos_flag                         false
% 0.83/1.00  --inst_sos_phase                        true
% 0.83/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/1.00  --inst_lit_sel_side                     num_symb
% 0.83/1.00  --inst_solver_per_active                1400
% 0.83/1.00  --inst_solver_calls_frac                1.
% 0.83/1.00  --inst_passive_queue_type               priority_queues
% 0.83/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/1.00  --inst_passive_queues_freq              [25;2]
% 0.83/1.00  --inst_dismatching                      true
% 0.83/1.00  --inst_eager_unprocessed_to_passive     true
% 0.83/1.00  --inst_prop_sim_given                   true
% 0.83/1.00  --inst_prop_sim_new                     false
% 0.83/1.00  --inst_subs_new                         false
% 0.83/1.00  --inst_eq_res_simp                      false
% 0.83/1.00  --inst_subs_given                       false
% 0.83/1.00  --inst_orphan_elimination               true
% 0.83/1.00  --inst_learning_loop_flag               true
% 0.83/1.00  --inst_learning_start                   3000
% 0.83/1.00  --inst_learning_factor                  2
% 0.83/1.00  --inst_start_prop_sim_after_learn       3
% 0.83/1.00  --inst_sel_renew                        solver
% 0.83/1.00  --inst_lit_activity_flag                true
% 0.83/1.00  --inst_restr_to_given                   false
% 0.83/1.00  --inst_activity_threshold               500
% 0.83/1.00  --inst_out_proof                        true
% 0.83/1.00  
% 0.83/1.00  ------ Resolution Options
% 0.83/1.00  
% 0.83/1.00  --resolution_flag                       true
% 0.83/1.00  --res_lit_sel                           adaptive
% 0.83/1.00  --res_lit_sel_side                      none
% 0.83/1.00  --res_ordering                          kbo
% 0.83/1.00  --res_to_prop_solver                    active
% 0.83/1.00  --res_prop_simpl_new                    false
% 0.83/1.00  --res_prop_simpl_given                  true
% 0.83/1.00  --res_passive_queue_type                priority_queues
% 0.83/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/1.00  --res_passive_queues_freq               [15;5]
% 0.83/1.00  --res_forward_subs                      full
% 0.83/1.00  --res_backward_subs                     full
% 0.83/1.00  --res_forward_subs_resolution           true
% 0.83/1.00  --res_backward_subs_resolution          true
% 0.83/1.00  --res_orphan_elimination                true
% 0.83/1.00  --res_time_limit                        2.
% 0.83/1.00  --res_out_proof                         true
% 0.83/1.00  
% 0.83/1.00  ------ Superposition Options
% 0.83/1.00  
% 0.83/1.00  --superposition_flag                    true
% 0.83/1.00  --sup_passive_queue_type                priority_queues
% 0.83/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.83/1.00  --demod_completeness_check              fast
% 0.83/1.00  --demod_use_ground                      true
% 0.83/1.00  --sup_to_prop_solver                    passive
% 0.83/1.00  --sup_prop_simpl_new                    true
% 0.83/1.00  --sup_prop_simpl_given                  true
% 0.83/1.00  --sup_fun_splitting                     false
% 0.83/1.00  --sup_smt_interval                      50000
% 0.83/1.00  
% 0.83/1.00  ------ Superposition Simplification Setup
% 0.83/1.00  
% 0.83/1.00  --sup_indices_passive                   []
% 0.83/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.00  --sup_full_bw                           [BwDemod]
% 0.83/1.00  --sup_immed_triv                        [TrivRules]
% 0.83/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.00  --sup_immed_bw_main                     []
% 0.83/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.00  
% 0.83/1.00  ------ Combination Options
% 0.83/1.00  
% 0.83/1.00  --comb_res_mult                         3
% 0.83/1.00  --comb_sup_mult                         2
% 0.83/1.00  --comb_inst_mult                        10
% 0.83/1.00  
% 0.83/1.00  ------ Debug Options
% 0.83/1.00  
% 0.83/1.00  --dbg_backtrace                         false
% 0.83/1.00  --dbg_dump_prop_clauses                 false
% 0.83/1.00  --dbg_dump_prop_clauses_file            -
% 0.83/1.00  --dbg_out_stat                          false
% 0.83/1.00  ------ Parsing...
% 0.83/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.83/1.00  
% 0.83/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s
% 0.83/1.00  
% 0.83/1.00  % SZS status Theorem for theBenchmark.p
% 0.83/1.00  
% 0.83/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.83/1.00  
% 0.83/1.00  fof(f5,axiom,(
% 0.83/1.00    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> r1_relat_2(X0,k3_relat_1(X0))))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f15,plain,(
% 0.83/1.00    ! [X0] : ((v1_relat_2(X0) <=> r1_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(ennf_transformation,[],[f5])).
% 0.83/1.00  
% 0.83/1.00  fof(f27,plain,(
% 0.83/1.00    ! [X0] : (((v1_relat_2(X0) | ~r1_relat_2(X0,k3_relat_1(X0))) & (r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(nnf_transformation,[],[f15])).
% 0.83/1.00  
% 0.83/1.00  fof(f46,plain,(
% 0.83/1.00    ( ! [X0] : (r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f27])).
% 0.83/1.00  
% 0.83/1.00  fof(f7,axiom,(
% 0.83/1.00    ! [X0] : (v1_relat_1(X0) => (v1_wellord1(X0) <=> r1_wellord1(X0,k3_relat_1(X0))))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f18,plain,(
% 0.83/1.00    ! [X0] : ((v1_wellord1(X0) <=> r1_wellord1(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(ennf_transformation,[],[f7])).
% 0.83/1.00  
% 0.83/1.00  fof(f28,plain,(
% 0.83/1.00    ! [X0] : (((v1_wellord1(X0) | ~r1_wellord1(X0,k3_relat_1(X0))) & (r1_wellord1(X0,k3_relat_1(X0)) | ~v1_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(nnf_transformation,[],[f18])).
% 0.83/1.00  
% 0.83/1.00  fof(f53,plain,(
% 0.83/1.00    ( ! [X0] : (r1_wellord1(X0,k3_relat_1(X0)) | ~v1_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f28])).
% 0.83/1.00  
% 0.83/1.00  fof(f3,axiom,(
% 0.83/1.00    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> r8_relat_2(X0,k3_relat_1(X0))))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f13,plain,(
% 0.83/1.00    ! [X0] : ((v8_relat_2(X0) <=> r8_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(ennf_transformation,[],[f3])).
% 0.83/1.00  
% 0.83/1.00  fof(f24,plain,(
% 0.83/1.00    ! [X0] : (((v8_relat_2(X0) | ~r8_relat_2(X0,k3_relat_1(X0))) & (r8_relat_2(X0,k3_relat_1(X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(nnf_transformation,[],[f13])).
% 0.83/1.00  
% 0.83/1.00  fof(f38,plain,(
% 0.83/1.00    ( ! [X0] : (r8_relat_2(X0,k3_relat_1(X0)) | ~v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f24])).
% 0.83/1.00  
% 0.83/1.00  fof(f2,axiom,(
% 0.83/1.00    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> r6_relat_2(X0,k3_relat_1(X0))))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f12,plain,(
% 0.83/1.00    ! [X0] : ((v6_relat_2(X0) <=> r6_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(ennf_transformation,[],[f2])).
% 0.83/1.00  
% 0.83/1.00  fof(f23,plain,(
% 0.83/1.00    ! [X0] : (((v6_relat_2(X0) | ~r6_relat_2(X0,k3_relat_1(X0))) & (r6_relat_2(X0,k3_relat_1(X0)) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(nnf_transformation,[],[f12])).
% 0.83/1.00  
% 0.83/1.00  fof(f36,plain,(
% 0.83/1.00    ( ! [X0] : (r6_relat_2(X0,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f23])).
% 0.83/1.00  
% 0.83/1.00  fof(f1,axiom,(
% 0.83/1.00    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> r4_relat_2(X0,k3_relat_1(X0))))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f11,plain,(
% 0.83/1.00    ! [X0] : ((v4_relat_2(X0) <=> r4_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(ennf_transformation,[],[f1])).
% 0.83/1.00  
% 0.83/1.00  fof(f22,plain,(
% 0.83/1.00    ! [X0] : (((v4_relat_2(X0) | ~r4_relat_2(X0,k3_relat_1(X0))) & (r4_relat_2(X0,k3_relat_1(X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(nnf_transformation,[],[f11])).
% 0.83/1.00  
% 0.83/1.00  fof(f34,plain,(
% 0.83/1.00    ( ! [X0] : (r4_relat_2(X0,k3_relat_1(X0)) | ~v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f22])).
% 0.83/1.00  
% 0.83/1.00  fof(f4,axiom,(
% 0.83/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_wellord1(X0,X1) <=> (r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f14,plain,(
% 0.83/1.00    ! [X0] : (! [X1] : (r2_wellord1(X0,X1) <=> (r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(ennf_transformation,[],[f4])).
% 0.83/1.00  
% 0.83/1.00  fof(f25,plain,(
% 0.83/1.00    ! [X0] : (! [X1] : ((r2_wellord1(X0,X1) | (~r1_wellord1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1))) & ((r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)) | ~r2_wellord1(X0,X1))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(nnf_transformation,[],[f14])).
% 0.83/1.00  
% 0.83/1.00  fof(f26,plain,(
% 0.83/1.00    ! [X0] : (! [X1] : ((r2_wellord1(X0,X1) | ~r1_wellord1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1)) & ((r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)) | ~r2_wellord1(X0,X1))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(flattening,[],[f25])).
% 0.83/1.00  
% 0.83/1.00  fof(f45,plain,(
% 0.83/1.00    ( ! [X0,X1] : (r2_wellord1(X0,X1) | ~r1_wellord1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f26])).
% 0.83/1.00  
% 0.83/1.00  fof(f6,axiom,(
% 0.83/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ((v1_wellord1(X0) => v1_wellord1(X1)) & (v4_relat_2(X0) => v4_relat_2(X1)) & (v6_relat_2(X0) => v6_relat_2(X1)) & (v8_relat_2(X0) => v8_relat_2(X1)) & (v1_relat_2(X0) => v1_relat_2(X1)))))))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f16,plain,(
% 0.83/1.00    ! [X0] : (! [X1] : (! [X2] : ((((v1_wellord1(X1) | ~v1_wellord1(X0)) & (v4_relat_2(X1) | ~v4_relat_2(X0)) & (v6_relat_2(X1) | ~v6_relat_2(X0)) & (v8_relat_2(X1) | ~v8_relat_2(X0)) & (v1_relat_2(X1) | ~v1_relat_2(X0))) | ~r3_wellord1(X0,X1,X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(ennf_transformation,[],[f6])).
% 0.83/1.00  
% 0.83/1.00  fof(f17,plain,(
% 0.83/1.00    ! [X0] : (! [X1] : (! [X2] : (((v1_wellord1(X1) | ~v1_wellord1(X0)) & (v4_relat_2(X1) | ~v4_relat_2(X0)) & (v6_relat_2(X1) | ~v6_relat_2(X0)) & (v8_relat_2(X1) | ~v8_relat_2(X0)) & (v1_relat_2(X1) | ~v1_relat_2(X0))) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(flattening,[],[f16])).
% 0.83/1.00  
% 0.83/1.00  fof(f51,plain,(
% 0.83/1.00    ( ! [X2,X0,X1] : (v4_relat_2(X1) | ~v4_relat_2(X0) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f17])).
% 0.83/1.00  
% 0.83/1.00  fof(f9,conjecture,(
% 0.83/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => v2_wellord1(X1)))))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f10,negated_conjecture,(
% 0.83/1.00    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => v2_wellord1(X1)))))),
% 0.83/1.00    inference(negated_conjecture,[],[f9])).
% 0.83/1.00  
% 0.83/1.00  fof(f20,plain,(
% 0.83/1.00    ? [X0] : (? [X1] : (? [X2] : ((~v2_wellord1(X1) & (r3_wellord1(X0,X1,X2) & v2_wellord1(X0))) & (v1_funct_1(X2) & v1_relat_1(X2))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.83/1.00    inference(ennf_transformation,[],[f10])).
% 0.83/1.00  
% 0.83/1.00  fof(f21,plain,(
% 0.83/1.00    ? [X0] : (? [X1] : (? [X2] : (~v2_wellord1(X1) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.83/1.00    inference(flattening,[],[f20])).
% 0.83/1.00  
% 0.83/1.00  fof(f32,plain,(
% 0.83/1.00    ( ! [X0,X1] : (? [X2] : (~v2_wellord1(X1) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) => (~v2_wellord1(X1) & r3_wellord1(X0,X1,sK2) & v2_wellord1(X0) & v1_funct_1(sK2) & v1_relat_1(sK2))) )),
% 0.83/1.00    introduced(choice_axiom,[])).
% 0.83/1.00  
% 0.83/1.00  fof(f31,plain,(
% 0.83/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~v2_wellord1(X1) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~v2_wellord1(sK1) & r3_wellord1(X0,sK1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(sK1))) )),
% 0.83/1.00    introduced(choice_axiom,[])).
% 0.83/1.00  
% 0.83/1.00  fof(f30,plain,(
% 0.83/1.00    ? [X0] : (? [X1] : (? [X2] : (~v2_wellord1(X1) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~v2_wellord1(X1) & r3_wellord1(sK0,X1,X2) & v2_wellord1(sK0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.83/1.00    introduced(choice_axiom,[])).
% 0.83/1.00  
% 0.83/1.00  fof(f33,plain,(
% 0.83/1.00    ((~v2_wellord1(sK1) & r3_wellord1(sK0,sK1,sK2) & v2_wellord1(sK0) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.83/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f32,f31,f30])).
% 0.83/1.00  
% 0.83/1.00  fof(f62,plain,(
% 0.83/1.00    r3_wellord1(sK0,sK1,sK2)),
% 0.83/1.00    inference(cnf_transformation,[],[f33])).
% 0.83/1.00  
% 0.83/1.00  fof(f57,plain,(
% 0.83/1.00    v1_relat_1(sK0)),
% 0.83/1.00    inference(cnf_transformation,[],[f33])).
% 0.83/1.00  
% 0.83/1.00  fof(f58,plain,(
% 0.83/1.00    v1_relat_1(sK1)),
% 0.83/1.00    inference(cnf_transformation,[],[f33])).
% 0.83/1.00  
% 0.83/1.00  fof(f59,plain,(
% 0.83/1.00    v1_relat_1(sK2)),
% 0.83/1.00    inference(cnf_transformation,[],[f33])).
% 0.83/1.00  
% 0.83/1.00  fof(f60,plain,(
% 0.83/1.00    v1_funct_1(sK2)),
% 0.83/1.00    inference(cnf_transformation,[],[f33])).
% 0.83/1.00  
% 0.83/1.00  fof(f61,plain,(
% 0.83/1.00    v2_wellord1(sK0)),
% 0.83/1.00    inference(cnf_transformation,[],[f33])).
% 0.83/1.00  
% 0.83/1.00  fof(f8,axiom,(
% 0.83/1.00    ! [X0] : (v1_relat_1(X0) => (r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)))),
% 0.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.83/1.00  
% 0.83/1.00  fof(f19,plain,(
% 0.83/1.00    ! [X0] : ((r2_wellord1(X0,k3_relat_1(X0)) <=> v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(ennf_transformation,[],[f8])).
% 0.83/1.00  
% 0.83/1.00  fof(f29,plain,(
% 0.83/1.00    ! [X0] : (((r2_wellord1(X0,k3_relat_1(X0)) | ~v2_wellord1(X0)) & (v2_wellord1(X0) | ~r2_wellord1(X0,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 0.83/1.00    inference(nnf_transformation,[],[f19])).
% 0.83/1.00  
% 0.83/1.00  fof(f56,plain,(
% 0.83/1.00    ( ! [X0] : (r2_wellord1(X0,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f29])).
% 0.83/1.00  
% 0.83/1.00  fof(f35,plain,(
% 0.83/1.00    ( ! [X0] : (v4_relat_2(X0) | ~r4_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f22])).
% 0.83/1.00  
% 0.83/1.00  fof(f42,plain,(
% 0.83/1.00    ( ! [X0,X1] : (r4_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f26])).
% 0.83/1.00  
% 0.83/1.00  fof(f52,plain,(
% 0.83/1.00    ( ! [X2,X0,X1] : (v1_wellord1(X1) | ~v1_wellord1(X0) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f17])).
% 0.83/1.00  
% 0.83/1.00  fof(f50,plain,(
% 0.83/1.00    ( ! [X2,X0,X1] : (v6_relat_2(X1) | ~v6_relat_2(X0) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f17])).
% 0.83/1.00  
% 0.83/1.00  fof(f49,plain,(
% 0.83/1.00    ( ! [X2,X0,X1] : (v8_relat_2(X1) | ~v8_relat_2(X0) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f17])).
% 0.83/1.00  
% 0.83/1.00  fof(f48,plain,(
% 0.83/1.00    ( ! [X2,X0,X1] : (v1_relat_2(X1) | ~v1_relat_2(X0) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f17])).
% 0.83/1.00  
% 0.83/1.00  fof(f40,plain,(
% 0.83/1.00    ( ! [X0,X1] : (r1_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f26])).
% 0.83/1.00  
% 0.83/1.00  fof(f47,plain,(
% 0.83/1.00    ( ! [X0] : (v1_relat_2(X0) | ~r1_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f27])).
% 0.83/1.00  
% 0.83/1.00  fof(f44,plain,(
% 0.83/1.00    ( ! [X0,X1] : (r1_wellord1(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f26])).
% 0.83/1.00  
% 0.83/1.00  fof(f54,plain,(
% 0.83/1.00    ( ! [X0] : (v1_wellord1(X0) | ~r1_wellord1(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f28])).
% 0.83/1.00  
% 0.83/1.00  fof(f39,plain,(
% 0.83/1.00    ( ! [X0] : (v8_relat_2(X0) | ~r8_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f24])).
% 0.83/1.00  
% 0.83/1.00  fof(f41,plain,(
% 0.83/1.00    ( ! [X0,X1] : (r8_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f26])).
% 0.83/1.00  
% 0.83/1.00  fof(f37,plain,(
% 0.83/1.00    ( ! [X0] : (v6_relat_2(X0) | ~r6_relat_2(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f23])).
% 0.83/1.00  
% 0.83/1.00  fof(f43,plain,(
% 0.83/1.00    ( ! [X0,X1] : (r6_relat_2(X0,X1) | ~r2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f26])).
% 0.83/1.00  
% 0.83/1.00  fof(f55,plain,(
% 0.83/1.00    ( ! [X0] : (v2_wellord1(X0) | ~r2_wellord1(X0,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.83/1.00    inference(cnf_transformation,[],[f29])).
% 0.83/1.00  
% 0.83/1.00  fof(f63,plain,(
% 0.83/1.00    ~v2_wellord1(sK1)),
% 0.83/1.00    inference(cnf_transformation,[],[f33])).
% 0.83/1.00  
% 0.83/1.00  cnf(c_13,plain,
% 0.83/1.00      ( r1_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v1_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f46]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_20,plain,
% 0.83/1.00      ( r1_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v1_wellord1(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f53]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_5,plain,
% 0.83/1.00      ( r8_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v8_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f38]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_3,plain,
% 0.83/1.00      ( r6_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v6_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f36]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_1,plain,
% 0.83/1.00      ( r4_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | ~ v4_relat_2(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f34]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_6,plain,
% 0.83/1.00      ( ~ r1_relat_2(X0,X1)
% 0.83/1.00      | ~ r1_wellord1(X0,X1)
% 0.83/1.00      | r2_wellord1(X0,X1)
% 0.83/1.00      | ~ r8_relat_2(X0,X1)
% 0.83/1.00      | ~ r6_relat_2(X0,X1)
% 0.83/1.00      | ~ r4_relat_2(X0,X1)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f45]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_331,plain,
% 0.83/1.00      ( ~ r1_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ r1_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | r2_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ r8_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ r6_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | ~ v4_relat_2(X0) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_1,c_6]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_381,plain,
% 0.83/1.00      ( ~ r1_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ r1_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | r2_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ r8_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v6_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | ~ v4_relat_2(X0) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_3,c_331]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_433,plain,
% 0.83/1.00      ( ~ r1_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ r1_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | r2_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v8_relat_2(X0)
% 0.83/1.00      | ~ v6_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | ~ v4_relat_2(X0) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_5,c_381]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_485,plain,
% 0.83/1.00      ( ~ r1_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | r2_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v1_wellord1(X0)
% 0.83/1.00      | ~ v8_relat_2(X0)
% 0.83/1.00      | ~ v6_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | ~ v4_relat_2(X0) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_20,c_433]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_537,plain,
% 0.83/1.00      ( r2_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v1_wellord1(X0)
% 0.83/1.00      | ~ v1_relat_2(X0)
% 0.83/1.00      | ~ v8_relat_2(X0)
% 0.83/1.00      | ~ v6_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | ~ v4_relat_2(X0) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_13,c_485]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_15,plain,
% 0.83/1.00      ( ~ r3_wellord1(X0,X1,X2)
% 0.83/1.00      | ~ v1_funct_1(X2)
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | ~ v1_relat_1(X2)
% 0.83/1.00      | ~ v1_relat_1(X1)
% 0.83/1.00      | ~ v4_relat_2(X0)
% 0.83/1.00      | v4_relat_2(X1) ),
% 0.83/1.00      inference(cnf_transformation,[],[f51]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_24,negated_conjecture,
% 0.83/1.00      ( r3_wellord1(sK0,sK1,sK2) ),
% 0.83/1.00      inference(cnf_transformation,[],[f62]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_619,plain,
% 0.83/1.00      ( ~ v1_funct_1(sK2)
% 0.83/1.00      | ~ v1_relat_1(sK2)
% 0.83/1.00      | ~ v1_relat_1(sK0)
% 0.83/1.00      | ~ v1_relat_1(sK1)
% 0.83/1.00      | ~ v4_relat_2(sK0)
% 0.83/1.00      | v4_relat_2(sK1) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_15,c_24]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_29,negated_conjecture,
% 0.83/1.00      ( v1_relat_1(sK0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f57]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_28,negated_conjecture,
% 0.83/1.00      ( v1_relat_1(sK1) ),
% 0.83/1.00      inference(cnf_transformation,[],[f58]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_27,negated_conjecture,
% 0.83/1.00      ( v1_relat_1(sK2) ),
% 0.83/1.00      inference(cnf_transformation,[],[f59]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_26,negated_conjecture,
% 0.83/1.00      ( v1_funct_1(sK2) ),
% 0.83/1.00      inference(cnf_transformation,[],[f60]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_25,negated_conjecture,
% 0.83/1.00      ( v2_wellord1(sK0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f61]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_21,plain,
% 0.83/1.00      ( r2_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v2_wellord1(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f56]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_39,plain,
% 0.83/1.00      ( r2_wellord1(sK0,k3_relat_1(sK0))
% 0.83/1.00      | ~ v2_wellord1(sK0)
% 0.83/1.00      | ~ v1_relat_1(sK0) ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_0,plain,
% 0.83/1.00      ( ~ r4_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | v4_relat_2(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f35]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_9,plain,
% 0.83/1.00      ( ~ r2_wellord1(X0,X1) | r4_relat_2(X0,X1) | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f42]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_355,plain,
% 0.83/1.00      ( ~ r2_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | v4_relat_2(X0) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_0,c_9]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_357,plain,
% 0.83/1.00      ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
% 0.83/1.00      | ~ v1_relat_1(sK0)
% 0.83/1.00      | v4_relat_2(sK0) ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_355]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_621,plain,
% 0.83/1.00      ( v4_relat_2(sK1) ),
% 0.83/1.00      inference(global_propositional_subsumption,
% 0.83/1.00                [status(thm)],
% 0.83/1.00                [c_619,c_29,c_28,c_27,c_26,c_25,c_39,c_357]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_650,plain,
% 0.83/1.00      ( r2_wellord1(sK1,k3_relat_1(sK1))
% 0.83/1.00      | ~ v1_wellord1(sK1)
% 0.83/1.00      | ~ v1_relat_2(sK1)
% 0.83/1.00      | ~ v8_relat_2(sK1)
% 0.83/1.00      | ~ v6_relat_2(sK1)
% 0.83/1.00      | ~ v1_relat_1(sK1) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_537,c_621]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_14,plain,
% 0.83/1.00      ( ~ r3_wellord1(X0,X1,X2)
% 0.83/1.00      | ~ v1_funct_1(X2)
% 0.83/1.00      | ~ v1_wellord1(X0)
% 0.83/1.00      | v1_wellord1(X1)
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | ~ v1_relat_1(X2)
% 0.83/1.00      | ~ v1_relat_1(X1) ),
% 0.83/1.00      inference(cnf_transformation,[],[f52]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_629,plain,
% 0.83/1.00      ( ~ v1_funct_1(sK2)
% 0.83/1.00      | ~ v1_wellord1(sK0)
% 0.83/1.00      | v1_wellord1(sK1)
% 0.83/1.00      | ~ v1_relat_1(sK2)
% 0.83/1.00      | ~ v1_relat_1(sK0)
% 0.83/1.00      | ~ v1_relat_1(sK1) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_14,c_24]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_16,plain,
% 0.83/1.00      ( ~ r3_wellord1(X0,X1,X2)
% 0.83/1.00      | ~ v1_funct_1(X2)
% 0.83/1.00      | ~ v6_relat_2(X0)
% 0.83/1.00      | v6_relat_2(X1)
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | ~ v1_relat_1(X2)
% 0.83/1.00      | ~ v1_relat_1(X1) ),
% 0.83/1.00      inference(cnf_transformation,[],[f50]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_609,plain,
% 0.83/1.00      ( ~ v1_funct_1(sK2)
% 0.83/1.00      | ~ v6_relat_2(sK0)
% 0.83/1.00      | v6_relat_2(sK1)
% 0.83/1.00      | ~ v1_relat_1(sK2)
% 0.83/1.00      | ~ v1_relat_1(sK0)
% 0.83/1.00      | ~ v1_relat_1(sK1) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_16,c_24]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_17,plain,
% 0.83/1.00      ( ~ r3_wellord1(X0,X1,X2)
% 0.83/1.00      | ~ v1_funct_1(X2)
% 0.83/1.00      | ~ v8_relat_2(X0)
% 0.83/1.00      | v8_relat_2(X1)
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | ~ v1_relat_1(X2)
% 0.83/1.00      | ~ v1_relat_1(X1) ),
% 0.83/1.00      inference(cnf_transformation,[],[f49]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_599,plain,
% 0.83/1.00      ( ~ v1_funct_1(sK2)
% 0.83/1.00      | ~ v8_relat_2(sK0)
% 0.83/1.00      | v8_relat_2(sK1)
% 0.83/1.00      | ~ v1_relat_1(sK2)
% 0.83/1.00      | ~ v1_relat_1(sK0)
% 0.83/1.00      | ~ v1_relat_1(sK1) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_17,c_24]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_18,plain,
% 0.83/1.00      ( ~ r3_wellord1(X0,X1,X2)
% 0.83/1.00      | ~ v1_funct_1(X2)
% 0.83/1.00      | ~ v1_relat_2(X0)
% 0.83/1.00      | v1_relat_2(X1)
% 0.83/1.00      | ~ v1_relat_1(X0)
% 0.83/1.00      | ~ v1_relat_1(X2)
% 0.83/1.00      | ~ v1_relat_1(X1) ),
% 0.83/1.00      inference(cnf_transformation,[],[f48]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_589,plain,
% 0.83/1.00      ( ~ v1_funct_1(sK2)
% 0.83/1.00      | ~ v1_relat_2(sK0)
% 0.83/1.00      | v1_relat_2(sK1)
% 0.83/1.00      | ~ v1_relat_1(sK2)
% 0.83/1.00      | ~ v1_relat_1(sK0)
% 0.83/1.00      | ~ v1_relat_1(sK1) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_18,c_24]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_11,plain,
% 0.83/1.00      ( r1_relat_2(X0,X1) | ~ r2_wellord1(X0,X1) | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f40]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_12,plain,
% 0.83/1.00      ( ~ r1_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | v1_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f47]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_563,plain,
% 0.83/1.00      ( ~ r2_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | v1_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_11,c_12]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_565,plain,
% 0.83/1.00      ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
% 0.83/1.00      | v1_relat_2(sK0)
% 0.83/1.00      | ~ v1_relat_1(sK0) ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_563]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_7,plain,
% 0.83/1.00      ( r1_wellord1(X0,X1) | ~ r2_wellord1(X0,X1) | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f44]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_19,plain,
% 0.83/1.00      ( ~ r1_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | v1_wellord1(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f54]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_511,plain,
% 0.83/1.00      ( ~ r2_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | v1_wellord1(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_7,c_19]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_513,plain,
% 0.83/1.00      ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
% 0.83/1.00      | v1_wellord1(sK0)
% 0.83/1.00      | ~ v1_relat_1(sK0) ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_511]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_4,plain,
% 0.83/1.00      ( ~ r8_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | v8_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f39]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_10,plain,
% 0.83/1.00      ( ~ r2_wellord1(X0,X1) | r8_relat_2(X0,X1) | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f41]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_459,plain,
% 0.83/1.00      ( ~ r2_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | v8_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_4,c_10]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_461,plain,
% 0.83/1.00      ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
% 0.83/1.00      | v8_relat_2(sK0)
% 0.83/1.00      | ~ v1_relat_1(sK0) ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_459]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_2,plain,
% 0.83/1.00      ( ~ r6_relat_2(X0,k3_relat_1(X0))
% 0.83/1.00      | v6_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f37]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_8,plain,
% 0.83/1.00      ( ~ r2_wellord1(X0,X1) | r6_relat_2(X0,X1) | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f43]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_407,plain,
% 0.83/1.00      ( ~ r2_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | v6_relat_2(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_2,c_8]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_409,plain,
% 0.83/1.00      ( ~ r2_wellord1(sK0,k3_relat_1(sK0))
% 0.83/1.00      | v6_relat_2(sK0)
% 0.83/1.00      | ~ v1_relat_1(sK0) ),
% 0.83/1.00      inference(instantiation,[status(thm)],[c_407]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_22,plain,
% 0.83/1.00      ( ~ r2_wellord1(X0,k3_relat_1(X0))
% 0.83/1.00      | v2_wellord1(X0)
% 0.83/1.00      | ~ v1_relat_1(X0) ),
% 0.83/1.00      inference(cnf_transformation,[],[f55]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_23,negated_conjecture,
% 0.83/1.00      ( ~ v2_wellord1(sK1) ),
% 0.83/1.00      inference(cnf_transformation,[],[f63]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(c_305,plain,
% 0.83/1.00      ( ~ r2_wellord1(sK1,k3_relat_1(sK1)) | ~ v1_relat_1(sK1) ),
% 0.83/1.00      inference(resolution,[status(thm)],[c_22,c_23]) ).
% 0.83/1.00  
% 0.83/1.00  cnf(contradiction,plain,
% 0.83/1.00      ( $false ),
% 0.83/1.00      inference(minisat,
% 0.83/1.00                [status(thm)],
% 0.83/1.00                [c_650,c_629,c_609,c_599,c_589,c_565,c_513,c_461,c_409,
% 0.83/1.00                 c_305,c_39,c_25,c_26,c_27,c_28,c_29]) ).
% 0.83/1.00  
% 0.83/1.00  
% 0.83/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.83/1.00  
% 0.83/1.00  ------                               Statistics
% 0.83/1.00  
% 0.83/1.00  ------ General
% 0.83/1.00  
% 0.83/1.00  abstr_ref_over_cycles:                  0
% 0.83/1.00  abstr_ref_under_cycles:                 0
% 0.83/1.00  gc_basic_clause_elim:                   0
% 0.83/1.00  forced_gc_time:                         0
% 0.83/1.00  parsing_time:                           0.01
% 0.83/1.00  unif_index_cands_time:                  0.
% 0.83/1.00  unif_index_add_time:                    0.
% 0.83/1.00  orderings_time:                         0.
% 0.83/1.00  out_proof_time:                         0.012
% 0.83/1.00  total_time:                             0.056
% 0.83/1.00  num_of_symbols:                         47
% 0.83/1.00  num_of_terms:                           262
% 0.83/1.00  
% 0.83/1.00  ------ Preprocessing
% 0.83/1.00  
% 0.83/1.00  num_of_splits:                          0
% 0.83/1.00  num_of_split_atoms:                     0
% 0.83/1.00  num_of_reused_defs:                     0
% 0.83/1.00  num_eq_ax_congr_red:                    0
% 0.83/1.00  num_of_sem_filtered_clauses:            0
% 0.83/1.00  num_of_subtypes:                        0
% 0.83/1.00  monotx_restored_types:                  0
% 0.83/1.00  sat_num_of_epr_types:                   0
% 0.83/1.00  sat_num_of_non_cyclic_types:            0
% 0.83/1.00  sat_guarded_non_collapsed_types:        0
% 0.83/1.00  num_pure_diseq_elim:                    0
% 0.83/1.00  simp_replaced_by:                       0
% 0.83/1.00  res_preprocessed:                       30
% 0.83/1.00  prep_upred:                             0
% 0.83/1.00  prep_unflattend:                        0
% 0.83/1.00  smt_new_axioms:                         0
% 0.83/1.00  pred_elim_cands:                        15
% 0.83/1.00  pred_elim:                              8
% 0.83/1.00  pred_elim_cl:                           0
% 0.83/1.00  pred_elim_cycles:                       8
% 0.83/1.00  merged_defs:                            0
% 0.83/1.00  merged_defs_ncl:                        0
% 0.83/1.00  bin_hyper_res:                          0
% 0.83/1.00  prep_cycles:                            1
% 0.83/1.00  pred_elim_time:                         0.
% 0.83/1.00  splitting_time:                         0.
% 0.83/1.00  sem_filter_time:                        0.
% 0.83/1.00  monotx_time:                            0.
% 0.83/1.00  subtype_inf_time:                       0.
% 0.83/1.00  
% 0.83/1.00  ------ Problem properties
% 0.83/1.00  
% 0.83/1.00  clauses:                                0
% 0.83/1.00  conjectures:                            0
% 0.83/1.00  epr:                                    0
% 0.83/1.00  horn:                                   0
% 0.83/1.00  ground:                                 0
% 0.83/1.00  unary:                                  0
% 0.83/1.00  binary:                                 0
% 0.83/1.00  lits:                                   0
% 0.83/1.00  lits_eq:                                0
% 0.83/1.00  fd_pure:                                0
% 0.83/1.00  fd_pseudo:                              0
% 0.83/1.00  fd_cond:                                0
% 0.83/1.00  fd_pseudo_cond:                         0
% 0.83/1.00  ac_symbols:                             undef
% 0.83/1.00  
% 0.83/1.00  ------ Propositional Solver
% 0.83/1.00  
% 0.83/1.00  prop_solver_calls:                      6
% 0.83/1.00  prop_fast_solver_calls:                 291
% 0.83/1.00  smt_solver_calls:                       0
% 0.83/1.00  smt_fast_solver_calls:                  0
% 0.83/1.00  prop_num_of_clauses:                    152
% 0.83/1.00  prop_preprocess_simplified:             886
% 0.83/1.00  prop_fo_subsumed:                       27
% 0.83/1.00  prop_solver_time:                       0.
% 0.83/1.00  smt_solver_time:                        0.
% 0.83/1.00  smt_fast_solver_time:                   0.
% 0.83/1.00  prop_fast_solver_time:                  0.
% 0.83/1.00  prop_unsat_core_time:                   0.
% 0.83/1.00  
% 0.83/1.00  ------ QBF
% 0.83/1.00  
% 0.83/1.00  qbf_q_res:                              0
% 0.83/1.00  qbf_num_tautologies:                    0
% 0.83/1.00  qbf_prep_cycles:                        0
% 0.83/1.00  
% 0.83/1.00  ------ BMC1
% 0.83/1.00  
% 0.83/1.00  bmc1_current_bound:                     -1
% 0.83/1.00  bmc1_last_solved_bound:                 -1
% 0.83/1.00  bmc1_unsat_core_size:                   -1
% 0.83/1.00  bmc1_unsat_core_parents_size:           -1
% 0.83/1.00  bmc1_merge_next_fun:                    0
% 0.83/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.83/1.00  
% 0.83/1.00  ------ Instantiation
% 0.83/1.00  
% 0.83/1.00  inst_num_of_clauses:                    undef
% 0.83/1.00  inst_num_in_passive:                    undef
% 0.83/1.00  inst_num_in_active:                     0
% 0.83/1.00  inst_num_in_unprocessed:                0
% 0.83/1.00  inst_num_of_loops:                      0
% 0.83/1.00  inst_num_of_learning_restarts:          0
% 0.83/1.00  inst_num_moves_active_passive:          0
% 0.83/1.00  inst_lit_activity:                      0
% 0.83/1.00  inst_lit_activity_moves:                0
% 0.83/1.00  inst_num_tautologies:                   0
% 0.83/1.00  inst_num_prop_implied:                  0
% 0.83/1.00  inst_num_existing_simplified:           0
% 0.83/1.00  inst_num_eq_res_simplified:             0
% 0.83/1.00  inst_num_child_elim:                    0
% 0.83/1.00  inst_num_of_dismatching_blockings:      0
% 0.83/1.00  inst_num_of_non_proper_insts:           0
% 0.83/1.00  inst_num_of_duplicates:                 0
% 0.83/1.00  inst_inst_num_from_inst_to_res:         0
% 0.83/1.00  inst_dismatching_checking_time:         0.
% 0.83/1.00  
% 0.83/1.00  ------ Resolution
% 0.83/1.00  
% 0.83/1.00  res_num_of_clauses:                     30
% 0.83/1.00  res_num_in_passive:                     0
% 0.83/1.00  res_num_in_active:                      0
% 0.83/1.00  res_num_of_loops:                       31
% 0.83/1.00  res_forward_subset_subsumed:            0
% 0.83/1.00  res_backward_subset_subsumed:           0
% 0.83/1.00  res_forward_subsumed:                   0
% 0.83/1.00  res_backward_subsumed:                  0
% 0.83/1.00  res_forward_subsumption_resolution:     0
% 0.83/1.00  res_backward_subsumption_resolution:    0
% 0.83/1.00  res_clause_to_clause_subsumption:       0
% 0.83/1.00  res_orphan_elimination:                 0
% 0.83/1.00  res_tautology_del:                      12
% 0.83/1.00  res_num_eq_res_simplified:              0
% 0.83/1.00  res_num_sel_changes:                    0
% 0.83/1.00  res_moves_from_active_to_pass:          0
% 0.83/1.00  
% 0.83/1.00  ------ Superposition
% 0.83/1.00  
% 0.83/1.00  sup_time_total:                         0.
% 0.83/1.00  sup_time_generating:                    0.
% 0.83/1.00  sup_time_sim_full:                      0.
% 0.83/1.00  sup_time_sim_immed:                     0.
% 0.83/1.00  
% 0.83/1.00  sup_num_of_clauses:                     undef
% 0.83/1.00  sup_num_in_active:                      undef
% 0.83/1.00  sup_num_in_passive:                     undef
% 0.83/1.00  sup_num_of_loops:                       0
% 0.83/1.00  sup_fw_superposition:                   0
% 0.83/1.00  sup_bw_superposition:                   0
% 0.83/1.00  sup_immediate_simplified:               0
% 0.83/1.00  sup_given_eliminated:                   0
% 0.83/1.00  comparisons_done:                       0
% 0.83/1.00  comparisons_avoided:                    0
% 0.83/1.00  
% 0.83/1.00  ------ Simplifications
% 0.83/1.00  
% 0.83/1.00  
% 0.83/1.00  sim_fw_subset_subsumed:                 0
% 0.83/1.00  sim_bw_subset_subsumed:                 0
% 0.83/1.00  sim_fw_subsumed:                        0
% 0.83/1.00  sim_bw_subsumed:                        0
% 0.83/1.00  sim_fw_subsumption_res:                 0
% 0.83/1.00  sim_bw_subsumption_res:                 0
% 0.83/1.00  sim_tautology_del:                      0
% 0.83/1.00  sim_eq_tautology_del:                   0
% 0.83/1.00  sim_eq_res_simp:                        0
% 0.83/1.00  sim_fw_demodulated:                     0
% 0.83/1.00  sim_bw_demodulated:                     0
% 0.83/1.00  sim_light_normalised:                   0
% 0.83/1.00  sim_joinable_taut:                      0
% 0.83/1.00  sim_joinable_simp:                      0
% 0.83/1.00  sim_ac_normalised:                      0
% 0.83/1.00  sim_smt_subsumption:                    0
% 0.83/1.00  
%------------------------------------------------------------------------------
