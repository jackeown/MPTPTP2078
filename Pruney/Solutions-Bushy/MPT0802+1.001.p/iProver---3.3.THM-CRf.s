%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0802+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:08 EST 2020

% Result     : Theorem 0.74s
% Output     : CNFRefutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 423 expanded)
%              Number of clauses        :   60 (  85 expanded)
%              Number of leaves         :    6 ( 139 expanded)
%              Depth                    :   14
%              Number of atoms          :  459 (3090 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_2(X1)
      | ~ v1_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,conjecture,(
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

fof(f4,negated_conjecture,(
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
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f14,plain,(
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

fof(f13,plain,(
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

fof(f12,plain,
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

fof(f15,plain,
    ( ~ v2_wellord1(sK1)
    & r3_wellord1(sK0,sK1,sK2)
    & v2_wellord1(sK0)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14,f13,f12])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( v8_relat_2(X1)
      | ~ v8_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v6_relat_2(X1)
      | ~ v6_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_2(X1)
      | ~ v4_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v1_wellord1(X1)
      | ~ v1_wellord1(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ~ v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_10,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_2(X0)
    | v1_relat_2(X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_325,plain,
    ( ~ r3_wellord1(X0,X1,sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_2(X0)
    | v1_relat_2(X1) ),
    inference(resolution,[status(thm)],[c_10,c_14])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_395,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ r3_wellord1(X0,X1,sK2)
    | ~ v1_relat_2(X0)
    | v1_relat_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_15])).

cnf(c_396,plain,
    ( ~ r3_wellord1(X0,X1,sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_2(X0)
    | v1_relat_2(X1) ),
    inference(renaming,[status(thm)],[c_395])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_488,plain,
    ( ~ r3_wellord1(sK0,X0,sK2)
    | ~ v1_relat_1(X0)
    | v1_relat_2(X0)
    | ~ v1_relat_2(sK0) ),
    inference(resolution,[status(thm)],[c_396,c_17])).

cnf(c_13,negated_conjecture,
    ( v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_2(X0)
    | ~ v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_31,plain,
    ( ~ v1_relat_1(sK0)
    | v1_relat_2(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_651,plain,
    ( v1_relat_2(X0)
    | ~ v1_relat_1(X0)
    | ~ r3_wellord1(sK0,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_17,c_13,c_31])).

cnf(c_652,plain,
    ( ~ r3_wellord1(sK0,X0,sK2)
    | ~ v1_relat_1(X0)
    | v1_relat_2(X0) ),
    inference(renaming,[status(thm)],[c_651])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_669,plain,
    ( ~ r3_wellord1(sK0,sK1,sK2)
    | v1_relat_2(sK1) ),
    inference(resolution,[status(thm)],[c_652,c_16])).

cnf(c_9,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v8_relat_2(X0)
    | v8_relat_2(X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_551,plain,
    ( ~ r3_wellord1(X0,sK1,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK1)
    | ~ v8_relat_2(X0)
    | v8_relat_2(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_555,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ r3_wellord1(X0,sK1,X1)
    | ~ v8_relat_2(X0)
    | v8_relat_2(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_16])).

cnf(c_556,plain,
    ( ~ r3_wellord1(X0,sK1,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v8_relat_2(X0)
    | v8_relat_2(sK1) ),
    inference(renaming,[status(thm)],[c_555])).

cnf(c_612,plain,
    ( ~ r3_wellord1(X0,sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | ~ v8_relat_2(X0)
    | v8_relat_2(sK1) ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_614,plain,
    ( ~ r3_wellord1(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | ~ v8_relat_2(sK0)
    | v8_relat_2(sK1) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_8,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v6_relat_2(X0)
    | v6_relat_2(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_317,plain,
    ( ~ r3_wellord1(X0,X1,sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK2)
    | ~ v6_relat_2(X0)
    | v6_relat_2(X1) ),
    inference(resolution,[status(thm)],[c_8,c_14])).

cnf(c_381,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ r3_wellord1(X0,X1,sK2)
    | ~ v6_relat_2(X0)
    | v6_relat_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_15])).

cnf(c_382,plain,
    ( ~ r3_wellord1(X0,X1,sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v6_relat_2(X0)
    | v6_relat_2(X1) ),
    inference(renaming,[status(thm)],[c_381])).

cnf(c_472,plain,
    ( ~ r3_wellord1(sK0,X0,sK2)
    | ~ v1_relat_1(X0)
    | v6_relat_2(X0)
    | ~ v6_relat_2(sK0) ),
    inference(resolution,[status(thm)],[c_382,c_17])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v6_relat_2(X0)
    | ~ v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_40,plain,
    ( ~ v1_relat_1(sK0)
    | v6_relat_2(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_537,plain,
    ( v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | ~ r3_wellord1(sK0,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_17,c_13,c_40])).

cnf(c_538,plain,
    ( ~ r3_wellord1(sK0,X0,sK2)
    | ~ v1_relat_1(X0)
    | v6_relat_2(X0) ),
    inference(renaming,[status(thm)],[c_537])).

cnf(c_546,plain,
    ( ~ r3_wellord1(sK0,sK1,sK2)
    | v6_relat_2(sK1) ),
    inference(resolution,[status(thm)],[c_538,c_16])).

cnf(c_7,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_2(X0)
    | v4_relat_2(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_313,plain,
    ( ~ r3_wellord1(X0,X1,sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_2(X0)
    | v4_relat_2(X1) ),
    inference(resolution,[status(thm)],[c_7,c_14])).

cnf(c_374,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ r3_wellord1(X0,X1,sK2)
    | ~ v4_relat_2(X0)
    | v4_relat_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_15])).

cnf(c_375,plain,
    ( ~ r3_wellord1(X0,X1,sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_2(X0)
    | v4_relat_2(X1) ),
    inference(renaming,[status(thm)],[c_374])).

cnf(c_406,plain,
    ( ~ r3_wellord1(sK0,X0,sK2)
    | ~ v1_relat_1(X0)
    | v4_relat_2(X0)
    | ~ v4_relat_2(sK0) ),
    inference(resolution,[status(thm)],[c_375,c_17])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v4_relat_2(X0)
    | ~ v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_37,plain,
    ( ~ v1_relat_1(sK0)
    | v4_relat_2(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_492,plain,
    ( v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | ~ r3_wellord1(sK0,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_17,c_13,c_37])).

cnf(c_493,plain,
    ( ~ r3_wellord1(sK0,X0,sK2)
    | ~ v1_relat_1(X0)
    | v4_relat_2(X0) ),
    inference(renaming,[status(thm)],[c_492])).

cnf(c_509,plain,
    ( ~ r3_wellord1(sK0,sK1,sK2)
    | v4_relat_2(sK1) ),
    inference(resolution,[status(thm)],[c_493,c_16])).

cnf(c_6,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_wellord1(X0)
    | v1_wellord1(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_309,plain,
    ( ~ r3_wellord1(X0,X1,sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK2)
    | ~ v1_wellord1(X0)
    | v1_wellord1(X1) ),
    inference(resolution,[status(thm)],[c_6,c_14])).

cnf(c_351,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ r3_wellord1(X0,X1,sK2)
    | ~ v1_wellord1(X0)
    | v1_wellord1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_15])).

cnf(c_352,plain,
    ( ~ r3_wellord1(X0,X1,sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_wellord1(X0)
    | v1_wellord1(X1) ),
    inference(renaming,[status(thm)],[c_351])).

cnf(c_362,plain,
    ( ~ r3_wellord1(sK0,X0,sK2)
    | ~ v1_relat_1(X0)
    | v1_wellord1(X0)
    | ~ v1_wellord1(sK0) ),
    inference(resolution,[status(thm)],[c_352,c_17])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_wellord1(X0)
    | ~ v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_43,plain,
    ( ~ v1_relat_1(sK0)
    | v1_wellord1(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_418,plain,
    ( v1_wellord1(X0)
    | ~ v1_relat_1(X0)
    | ~ r3_wellord1(sK0,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_17,c_13,c_43])).

cnf(c_419,plain,
    ( ~ r3_wellord1(sK0,X0,sK2)
    | ~ v1_relat_1(X0)
    | v1_wellord1(X0) ),
    inference(renaming,[status(thm)],[c_418])).

cnf(c_427,plain,
    ( ~ r3_wellord1(sK0,sK1,sK2)
    | v1_wellord1(sK1) ),
    inference(resolution,[status(thm)],[c_419,c_16])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_2(X0)
    | ~ v8_relat_2(X0)
    | ~ v4_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v1_wellord1(X0)
    | v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_269,plain,
    ( ~ v1_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | ~ v4_relat_2(sK1)
    | ~ v6_relat_2(sK1)
    | ~ v1_wellord1(sK1)
    | v2_wellord1(sK1) ),
    inference(resolution,[status(thm)],[c_0,c_16])).

cnf(c_11,negated_conjecture,
    ( ~ v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_342,plain,
    ( ~ v1_wellord1(sK1)
    | ~ v6_relat_2(sK1)
    | ~ v4_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | ~ v1_relat_2(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_269,c_11])).

cnf(c_343,plain,
    ( ~ v1_relat_2(sK1)
    | ~ v8_relat_2(sK1)
    | ~ v4_relat_2(sK1)
    | ~ v6_relat_2(sK1)
    | ~ v1_wellord1(sK1) ),
    inference(renaming,[status(thm)],[c_342])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v8_relat_2(X0)
    | ~ v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_34,plain,
    ( ~ v1_relat_1(sK0)
    | v8_relat_2(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_12,negated_conjecture,
    ( r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_669,c_614,c_546,c_509,c_427,c_343,c_34,c_12,c_13,c_14,c_15,c_17])).


%------------------------------------------------------------------------------
