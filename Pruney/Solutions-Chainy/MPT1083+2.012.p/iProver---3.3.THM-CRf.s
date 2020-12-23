%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:29 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 359 expanded)
%              Number of clauses        :   61 ( 108 expanded)
%              Number of leaves         :   16 ( 104 expanded)
%              Depth                    :   25
%              Number of atoms          :  356 (2174 expanded)
%              Number of equality atoms :  130 ( 411 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X1))
        & v1_funct_1(sK2)
        & v5_relat_1(sK2,X0)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
     => ( ? [X2] :
            ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1))
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK1,X0,X0)
        & v1_funct_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
                & v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,sK0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X1,sK0,sK0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30,f29,f28])).

fof(f52,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_610,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_232,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | sK0 != X2
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_233,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_235,plain,
    ( v1_partfun1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_233,c_23,c_22,c_20])).

cnf(c_15,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_272,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_273,plain,
    ( v4_relat_1(sK1,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_294,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_relat_1(X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_273])).

cnf(c_295,plain,
    ( ~ v1_partfun1(sK1,X0)
    | ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_383,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK0 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_235,c_295])).

cnf(c_384,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_457,plain,
    ( ~ v1_relat_1(sK1)
    | sP0_iProver_split
    | k1_relat_1(sK1) = sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_384])).

cnf(c_606,plain,
    ( k1_relat_1(sK1) = sK0
    | v1_relat_1(sK1) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_61,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_63,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_477,plain,
    ( k1_relat_1(sK1) = sK0
    | v1_relat_1(sK1) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_245,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_246,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_609,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_716,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_609])).

cnf(c_456,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_384])).

cnf(c_607,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_840,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_607])).

cnf(c_930,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_63,c_477,c_716,c_840])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_relat_1(X1) != k1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(k5_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_612,plain,
    ( k1_relat_1(X0) != k1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1610,plain,
    ( k1_relat_1(X0) != sK0
    | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(k5_relat_1(X1,sK1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_930,c_612])).

cnf(c_1753,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(k5_relat_1(X1,sK1))
    | k1_relat_1(X0) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1610,c_63,c_716])).

cnf(c_1754,plain,
    ( k1_relat_1(X0) != sK0
    | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(k5_relat_1(X1,sK1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1753])).

cnf(c_1763,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X0,sK1))
    | sK0 != X1
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1754])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_611,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1803,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X0,sK1))
    | sK0 != X1
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1763,c_611])).

cnf(c_1807,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(sK0))) = k1_relat_1(k5_relat_1(X0,sK1))
    | v1_relat_1(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1803])).

cnf(c_1816,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK0))) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_610,c_1807])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_336,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(resolution,[status(thm)],[c_2,c_7])).

cnf(c_18,negated_conjecture,
    ( v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_355,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_336,c_18])).

cnf(c_356,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_358,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_19])).

cnf(c_1822,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1816,c_358])).

cnf(c_459,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_918,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_459])).

cnf(c_460,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_709,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) != X0
    | k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_760,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(X0)
    | k1_relat_1(sK2) != k1_relat_1(X0)
    | k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_917,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1))
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_16,negated_conjecture,
    ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1822,c_918,c_917,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:21:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.72/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.00  
% 1.72/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.72/1.00  
% 1.72/1.00  ------  iProver source info
% 1.72/1.00  
% 1.72/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.72/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.72/1.00  git: non_committed_changes: false
% 1.72/1.00  git: last_make_outside_of_git: false
% 1.72/1.00  
% 1.72/1.00  ------ 
% 1.72/1.00  
% 1.72/1.00  ------ Input Options
% 1.72/1.00  
% 1.72/1.00  --out_options                           all
% 1.72/1.00  --tptp_safe_out                         true
% 1.72/1.00  --problem_path                          ""
% 1.72/1.00  --include_path                          ""
% 1.72/1.00  --clausifier                            res/vclausify_rel
% 1.72/1.00  --clausifier_options                    --mode clausify
% 1.72/1.00  --stdin                                 false
% 1.72/1.00  --stats_out                             all
% 1.72/1.00  
% 1.72/1.00  ------ General Options
% 1.72/1.00  
% 1.72/1.00  --fof                                   false
% 1.72/1.00  --time_out_real                         305.
% 1.72/1.00  --time_out_virtual                      -1.
% 1.72/1.00  --symbol_type_check                     false
% 1.72/1.00  --clausify_out                          false
% 1.72/1.00  --sig_cnt_out                           false
% 1.72/1.00  --trig_cnt_out                          false
% 1.72/1.00  --trig_cnt_out_tolerance                1.
% 1.72/1.00  --trig_cnt_out_sk_spl                   false
% 1.72/1.00  --abstr_cl_out                          false
% 1.72/1.00  
% 1.72/1.00  ------ Global Options
% 1.72/1.00  
% 1.72/1.00  --schedule                              default
% 1.72/1.00  --add_important_lit                     false
% 1.72/1.00  --prop_solver_per_cl                    1000
% 1.72/1.00  --min_unsat_core                        false
% 1.72/1.00  --soft_assumptions                      false
% 1.72/1.00  --soft_lemma_size                       3
% 1.72/1.00  --prop_impl_unit_size                   0
% 1.72/1.00  --prop_impl_unit                        []
% 1.72/1.00  --share_sel_clauses                     true
% 1.72/1.00  --reset_solvers                         false
% 1.72/1.00  --bc_imp_inh                            [conj_cone]
% 1.72/1.00  --conj_cone_tolerance                   3.
% 1.72/1.00  --extra_neg_conj                        none
% 1.72/1.00  --large_theory_mode                     true
% 1.72/1.00  --prolific_symb_bound                   200
% 1.72/1.00  --lt_threshold                          2000
% 1.72/1.00  --clause_weak_htbl                      true
% 1.72/1.00  --gc_record_bc_elim                     false
% 1.72/1.00  
% 1.72/1.00  ------ Preprocessing Options
% 1.72/1.00  
% 1.72/1.00  --preprocessing_flag                    true
% 1.72/1.00  --time_out_prep_mult                    0.1
% 1.72/1.00  --splitting_mode                        input
% 1.72/1.00  --splitting_grd                         true
% 1.72/1.00  --splitting_cvd                         false
% 1.72/1.00  --splitting_cvd_svl                     false
% 1.72/1.00  --splitting_nvd                         32
% 1.72/1.00  --sub_typing                            true
% 1.72/1.00  --prep_gs_sim                           true
% 1.72/1.00  --prep_unflatten                        true
% 1.72/1.00  --prep_res_sim                          true
% 1.72/1.00  --prep_upred                            true
% 1.72/1.00  --prep_sem_filter                       exhaustive
% 1.72/1.00  --prep_sem_filter_out                   false
% 1.72/1.00  --pred_elim                             true
% 1.72/1.00  --res_sim_input                         true
% 1.72/1.00  --eq_ax_congr_red                       true
% 1.72/1.00  --pure_diseq_elim                       true
% 1.72/1.00  --brand_transform                       false
% 1.72/1.00  --non_eq_to_eq                          false
% 1.72/1.00  --prep_def_merge                        true
% 1.72/1.00  --prep_def_merge_prop_impl              false
% 1.72/1.00  --prep_def_merge_mbd                    true
% 1.72/1.00  --prep_def_merge_tr_red                 false
% 1.72/1.00  --prep_def_merge_tr_cl                  false
% 1.72/1.00  --smt_preprocessing                     true
% 1.72/1.00  --smt_ac_axioms                         fast
% 1.72/1.00  --preprocessed_out                      false
% 1.72/1.00  --preprocessed_stats                    false
% 1.72/1.00  
% 1.72/1.00  ------ Abstraction refinement Options
% 1.72/1.00  
% 1.72/1.00  --abstr_ref                             []
% 1.72/1.00  --abstr_ref_prep                        false
% 1.72/1.00  --abstr_ref_until_sat                   false
% 1.72/1.00  --abstr_ref_sig_restrict                funpre
% 1.72/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/1.00  --abstr_ref_under                       []
% 1.72/1.00  
% 1.72/1.00  ------ SAT Options
% 1.72/1.00  
% 1.72/1.00  --sat_mode                              false
% 1.72/1.00  --sat_fm_restart_options                ""
% 1.72/1.00  --sat_gr_def                            false
% 1.72/1.00  --sat_epr_types                         true
% 1.72/1.00  --sat_non_cyclic_types                  false
% 1.72/1.00  --sat_finite_models                     false
% 1.72/1.00  --sat_fm_lemmas                         false
% 1.72/1.00  --sat_fm_prep                           false
% 1.72/1.00  --sat_fm_uc_incr                        true
% 1.72/1.00  --sat_out_model                         small
% 1.72/1.00  --sat_out_clauses                       false
% 1.72/1.00  
% 1.72/1.00  ------ QBF Options
% 1.72/1.00  
% 1.72/1.00  --qbf_mode                              false
% 1.72/1.00  --qbf_elim_univ                         false
% 1.72/1.00  --qbf_dom_inst                          none
% 1.72/1.00  --qbf_dom_pre_inst                      false
% 1.72/1.00  --qbf_sk_in                             false
% 1.72/1.00  --qbf_pred_elim                         true
% 1.72/1.00  --qbf_split                             512
% 1.72/1.00  
% 1.72/1.00  ------ BMC1 Options
% 1.72/1.00  
% 1.72/1.00  --bmc1_incremental                      false
% 1.72/1.00  --bmc1_axioms                           reachable_all
% 1.72/1.00  --bmc1_min_bound                        0
% 1.72/1.00  --bmc1_max_bound                        -1
% 1.72/1.00  --bmc1_max_bound_default                -1
% 1.72/1.00  --bmc1_symbol_reachability              true
% 1.72/1.00  --bmc1_property_lemmas                  false
% 1.72/1.00  --bmc1_k_induction                      false
% 1.72/1.00  --bmc1_non_equiv_states                 false
% 1.72/1.00  --bmc1_deadlock                         false
% 1.72/1.00  --bmc1_ucm                              false
% 1.72/1.00  --bmc1_add_unsat_core                   none
% 1.72/1.00  --bmc1_unsat_core_children              false
% 1.72/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/1.00  --bmc1_out_stat                         full
% 1.72/1.00  --bmc1_ground_init                      false
% 1.72/1.00  --bmc1_pre_inst_next_state              false
% 1.72/1.00  --bmc1_pre_inst_state                   false
% 1.72/1.00  --bmc1_pre_inst_reach_state             false
% 1.72/1.00  --bmc1_out_unsat_core                   false
% 1.72/1.00  --bmc1_aig_witness_out                  false
% 1.72/1.00  --bmc1_verbose                          false
% 1.72/1.00  --bmc1_dump_clauses_tptp                false
% 1.72/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.72/1.00  --bmc1_dump_file                        -
% 1.72/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.72/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.72/1.00  --bmc1_ucm_extend_mode                  1
% 1.72/1.00  --bmc1_ucm_init_mode                    2
% 1.72/1.00  --bmc1_ucm_cone_mode                    none
% 1.72/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.72/1.00  --bmc1_ucm_relax_model                  4
% 1.72/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.72/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/1.00  --bmc1_ucm_layered_model                none
% 1.72/1.00  --bmc1_ucm_max_lemma_size               10
% 1.72/1.00  
% 1.72/1.00  ------ AIG Options
% 1.72/1.00  
% 1.72/1.00  --aig_mode                              false
% 1.72/1.00  
% 1.72/1.00  ------ Instantiation Options
% 1.72/1.00  
% 1.72/1.00  --instantiation_flag                    true
% 1.72/1.00  --inst_sos_flag                         false
% 1.72/1.00  --inst_sos_phase                        true
% 1.72/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/1.00  --inst_lit_sel_side                     num_symb
% 1.72/1.00  --inst_solver_per_active                1400
% 1.72/1.00  --inst_solver_calls_frac                1.
% 1.72/1.00  --inst_passive_queue_type               priority_queues
% 1.72/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/1.00  --inst_passive_queues_freq              [25;2]
% 1.72/1.00  --inst_dismatching                      true
% 1.72/1.00  --inst_eager_unprocessed_to_passive     true
% 1.72/1.00  --inst_prop_sim_given                   true
% 1.72/1.00  --inst_prop_sim_new                     false
% 1.72/1.00  --inst_subs_new                         false
% 1.72/1.00  --inst_eq_res_simp                      false
% 1.72/1.00  --inst_subs_given                       false
% 1.72/1.00  --inst_orphan_elimination               true
% 1.72/1.00  --inst_learning_loop_flag               true
% 1.72/1.00  --inst_learning_start                   3000
% 1.72/1.00  --inst_learning_factor                  2
% 1.72/1.00  --inst_start_prop_sim_after_learn       3
% 1.72/1.00  --inst_sel_renew                        solver
% 1.72/1.00  --inst_lit_activity_flag                true
% 1.72/1.00  --inst_restr_to_given                   false
% 1.72/1.00  --inst_activity_threshold               500
% 1.72/1.00  --inst_out_proof                        true
% 1.72/1.00  
% 1.72/1.00  ------ Resolution Options
% 1.72/1.00  
% 1.72/1.00  --resolution_flag                       true
% 1.72/1.00  --res_lit_sel                           adaptive
% 1.72/1.00  --res_lit_sel_side                      none
% 1.72/1.00  --res_ordering                          kbo
% 1.72/1.00  --res_to_prop_solver                    active
% 1.72/1.00  --res_prop_simpl_new                    false
% 1.72/1.00  --res_prop_simpl_given                  true
% 1.72/1.00  --res_passive_queue_type                priority_queues
% 1.72/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/1.00  --res_passive_queues_freq               [15;5]
% 1.72/1.00  --res_forward_subs                      full
% 1.72/1.00  --res_backward_subs                     full
% 1.72/1.00  --res_forward_subs_resolution           true
% 1.72/1.00  --res_backward_subs_resolution          true
% 1.72/1.00  --res_orphan_elimination                true
% 1.72/1.00  --res_time_limit                        2.
% 1.72/1.00  --res_out_proof                         true
% 1.72/1.00  
% 1.72/1.00  ------ Superposition Options
% 1.72/1.00  
% 1.72/1.00  --superposition_flag                    true
% 1.72/1.00  --sup_passive_queue_type                priority_queues
% 1.72/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.72/1.00  --demod_completeness_check              fast
% 1.72/1.00  --demod_use_ground                      true
% 1.72/1.00  --sup_to_prop_solver                    passive
% 1.72/1.00  --sup_prop_simpl_new                    true
% 1.72/1.00  --sup_prop_simpl_given                  true
% 1.72/1.00  --sup_fun_splitting                     false
% 1.72/1.00  --sup_smt_interval                      50000
% 1.72/1.00  
% 1.72/1.00  ------ Superposition Simplification Setup
% 1.72/1.00  
% 1.72/1.00  --sup_indices_passive                   []
% 1.72/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.00  --sup_full_bw                           [BwDemod]
% 1.72/1.00  --sup_immed_triv                        [TrivRules]
% 1.72/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.00  --sup_immed_bw_main                     []
% 1.72/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.00  
% 1.72/1.00  ------ Combination Options
% 1.72/1.00  
% 1.72/1.00  --comb_res_mult                         3
% 1.72/1.00  --comb_sup_mult                         2
% 1.72/1.00  --comb_inst_mult                        10
% 1.72/1.00  
% 1.72/1.00  ------ Debug Options
% 1.72/1.00  
% 1.72/1.00  --dbg_backtrace                         false
% 1.72/1.00  --dbg_dump_prop_clauses                 false
% 1.72/1.00  --dbg_dump_prop_clauses_file            -
% 1.72/1.00  --dbg_out_stat                          false
% 1.72/1.00  ------ Parsing...
% 1.72/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.72/1.00  
% 1.72/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.72/1.00  
% 1.72/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.72/1.00  
% 1.72/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.72/1.00  ------ Proving...
% 1.72/1.00  ------ Problem Properties 
% 1.72/1.00  
% 1.72/1.00  
% 1.72/1.00  clauses                                 12
% 1.72/1.00  conjectures                             2
% 1.72/1.00  EPR                                     1
% 1.72/1.00  Horn                                    11
% 1.72/1.00  unary                                   7
% 1.72/1.00  binary                                  1
% 1.72/1.00  lits                                    23
% 1.72/1.00  lits eq                                 11
% 1.72/1.00  fd_pure                                 0
% 1.72/1.00  fd_pseudo                               0
% 1.72/1.00  fd_cond                                 0
% 1.72/1.00  fd_pseudo_cond                          0
% 1.72/1.00  AC symbols                              0
% 1.72/1.00  
% 1.72/1.00  ------ Schedule dynamic 5 is on 
% 1.72/1.00  
% 1.72/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.72/1.00  
% 1.72/1.00  
% 1.72/1.00  ------ 
% 1.72/1.00  Current options:
% 1.72/1.00  ------ 
% 1.72/1.00  
% 1.72/1.00  ------ Input Options
% 1.72/1.00  
% 1.72/1.00  --out_options                           all
% 1.72/1.00  --tptp_safe_out                         true
% 1.72/1.00  --problem_path                          ""
% 1.72/1.00  --include_path                          ""
% 1.72/1.00  --clausifier                            res/vclausify_rel
% 1.72/1.00  --clausifier_options                    --mode clausify
% 1.72/1.00  --stdin                                 false
% 1.72/1.00  --stats_out                             all
% 1.72/1.00  
% 1.72/1.00  ------ General Options
% 1.72/1.00  
% 1.72/1.00  --fof                                   false
% 1.72/1.00  --time_out_real                         305.
% 1.72/1.00  --time_out_virtual                      -1.
% 1.72/1.00  --symbol_type_check                     false
% 1.72/1.00  --clausify_out                          false
% 1.72/1.00  --sig_cnt_out                           false
% 1.72/1.00  --trig_cnt_out                          false
% 1.72/1.00  --trig_cnt_out_tolerance                1.
% 1.72/1.00  --trig_cnt_out_sk_spl                   false
% 1.72/1.00  --abstr_cl_out                          false
% 1.72/1.00  
% 1.72/1.00  ------ Global Options
% 1.72/1.00  
% 1.72/1.00  --schedule                              default
% 1.72/1.00  --add_important_lit                     false
% 1.72/1.00  --prop_solver_per_cl                    1000
% 1.72/1.00  --min_unsat_core                        false
% 1.72/1.00  --soft_assumptions                      false
% 1.72/1.00  --soft_lemma_size                       3
% 1.72/1.00  --prop_impl_unit_size                   0
% 1.72/1.00  --prop_impl_unit                        []
% 1.72/1.00  --share_sel_clauses                     true
% 1.72/1.00  --reset_solvers                         false
% 1.72/1.00  --bc_imp_inh                            [conj_cone]
% 1.72/1.00  --conj_cone_tolerance                   3.
% 1.72/1.00  --extra_neg_conj                        none
% 1.72/1.00  --large_theory_mode                     true
% 1.72/1.00  --prolific_symb_bound                   200
% 1.72/1.00  --lt_threshold                          2000
% 1.72/1.00  --clause_weak_htbl                      true
% 1.72/1.00  --gc_record_bc_elim                     false
% 1.72/1.00  
% 1.72/1.00  ------ Preprocessing Options
% 1.72/1.00  
% 1.72/1.00  --preprocessing_flag                    true
% 1.72/1.00  --time_out_prep_mult                    0.1
% 1.72/1.00  --splitting_mode                        input
% 1.72/1.00  --splitting_grd                         true
% 1.72/1.00  --splitting_cvd                         false
% 1.72/1.00  --splitting_cvd_svl                     false
% 1.72/1.00  --splitting_nvd                         32
% 1.72/1.00  --sub_typing                            true
% 1.72/1.00  --prep_gs_sim                           true
% 1.72/1.00  --prep_unflatten                        true
% 1.72/1.00  --prep_res_sim                          true
% 1.72/1.00  --prep_upred                            true
% 1.72/1.00  --prep_sem_filter                       exhaustive
% 1.72/1.00  --prep_sem_filter_out                   false
% 1.72/1.00  --pred_elim                             true
% 1.72/1.00  --res_sim_input                         true
% 1.72/1.00  --eq_ax_congr_red                       true
% 1.72/1.00  --pure_diseq_elim                       true
% 1.72/1.00  --brand_transform                       false
% 1.72/1.00  --non_eq_to_eq                          false
% 1.72/1.00  --prep_def_merge                        true
% 1.72/1.00  --prep_def_merge_prop_impl              false
% 1.72/1.00  --prep_def_merge_mbd                    true
% 1.72/1.00  --prep_def_merge_tr_red                 false
% 1.72/1.00  --prep_def_merge_tr_cl                  false
% 1.72/1.00  --smt_preprocessing                     true
% 1.72/1.00  --smt_ac_axioms                         fast
% 1.72/1.00  --preprocessed_out                      false
% 1.72/1.00  --preprocessed_stats                    false
% 1.72/1.00  
% 1.72/1.00  ------ Abstraction refinement Options
% 1.72/1.00  
% 1.72/1.00  --abstr_ref                             []
% 1.72/1.00  --abstr_ref_prep                        false
% 1.72/1.00  --abstr_ref_until_sat                   false
% 1.72/1.00  --abstr_ref_sig_restrict                funpre
% 1.72/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/1.00  --abstr_ref_under                       []
% 1.72/1.00  
% 1.72/1.00  ------ SAT Options
% 1.72/1.00  
% 1.72/1.00  --sat_mode                              false
% 1.72/1.00  --sat_fm_restart_options                ""
% 1.72/1.00  --sat_gr_def                            false
% 1.72/1.00  --sat_epr_types                         true
% 1.72/1.00  --sat_non_cyclic_types                  false
% 1.72/1.00  --sat_finite_models                     false
% 1.72/1.00  --sat_fm_lemmas                         false
% 1.72/1.00  --sat_fm_prep                           false
% 1.72/1.00  --sat_fm_uc_incr                        true
% 1.72/1.00  --sat_out_model                         small
% 1.72/1.00  --sat_out_clauses                       false
% 1.72/1.00  
% 1.72/1.00  ------ QBF Options
% 1.72/1.00  
% 1.72/1.00  --qbf_mode                              false
% 1.72/1.00  --qbf_elim_univ                         false
% 1.72/1.00  --qbf_dom_inst                          none
% 1.72/1.00  --qbf_dom_pre_inst                      false
% 1.72/1.00  --qbf_sk_in                             false
% 1.72/1.00  --qbf_pred_elim                         true
% 1.72/1.00  --qbf_split                             512
% 1.72/1.00  
% 1.72/1.00  ------ BMC1 Options
% 1.72/1.00  
% 1.72/1.00  --bmc1_incremental                      false
% 1.72/1.00  --bmc1_axioms                           reachable_all
% 1.72/1.00  --bmc1_min_bound                        0
% 1.72/1.00  --bmc1_max_bound                        -1
% 1.72/1.00  --bmc1_max_bound_default                -1
% 1.72/1.00  --bmc1_symbol_reachability              true
% 1.72/1.00  --bmc1_property_lemmas                  false
% 1.72/1.00  --bmc1_k_induction                      false
% 1.72/1.00  --bmc1_non_equiv_states                 false
% 1.72/1.00  --bmc1_deadlock                         false
% 1.72/1.00  --bmc1_ucm                              false
% 1.72/1.00  --bmc1_add_unsat_core                   none
% 1.72/1.00  --bmc1_unsat_core_children              false
% 1.72/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/1.00  --bmc1_out_stat                         full
% 1.72/1.00  --bmc1_ground_init                      false
% 1.72/1.00  --bmc1_pre_inst_next_state              false
% 1.72/1.00  --bmc1_pre_inst_state                   false
% 1.72/1.00  --bmc1_pre_inst_reach_state             false
% 1.72/1.00  --bmc1_out_unsat_core                   false
% 1.72/1.00  --bmc1_aig_witness_out                  false
% 1.72/1.00  --bmc1_verbose                          false
% 1.72/1.00  --bmc1_dump_clauses_tptp                false
% 1.72/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.72/1.00  --bmc1_dump_file                        -
% 1.72/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.72/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.72/1.00  --bmc1_ucm_extend_mode                  1
% 1.72/1.00  --bmc1_ucm_init_mode                    2
% 1.72/1.00  --bmc1_ucm_cone_mode                    none
% 1.72/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.72/1.00  --bmc1_ucm_relax_model                  4
% 1.72/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.72/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/1.00  --bmc1_ucm_layered_model                none
% 1.72/1.00  --bmc1_ucm_max_lemma_size               10
% 1.72/1.00  
% 1.72/1.00  ------ AIG Options
% 1.72/1.00  
% 1.72/1.00  --aig_mode                              false
% 1.72/1.00  
% 1.72/1.00  ------ Instantiation Options
% 1.72/1.00  
% 1.72/1.00  --instantiation_flag                    true
% 1.72/1.00  --inst_sos_flag                         false
% 1.72/1.00  --inst_sos_phase                        true
% 1.72/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/1.00  --inst_lit_sel_side                     none
% 1.72/1.00  --inst_solver_per_active                1400
% 1.72/1.00  --inst_solver_calls_frac                1.
% 1.72/1.00  --inst_passive_queue_type               priority_queues
% 1.72/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/1.00  --inst_passive_queues_freq              [25;2]
% 1.72/1.00  --inst_dismatching                      true
% 1.72/1.00  --inst_eager_unprocessed_to_passive     true
% 1.72/1.00  --inst_prop_sim_given                   true
% 1.72/1.00  --inst_prop_sim_new                     false
% 1.72/1.00  --inst_subs_new                         false
% 1.72/1.00  --inst_eq_res_simp                      false
% 1.72/1.00  --inst_subs_given                       false
% 1.72/1.00  --inst_orphan_elimination               true
% 1.72/1.00  --inst_learning_loop_flag               true
% 1.72/1.00  --inst_learning_start                   3000
% 1.72/1.00  --inst_learning_factor                  2
% 1.72/1.00  --inst_start_prop_sim_after_learn       3
% 1.72/1.00  --inst_sel_renew                        solver
% 1.72/1.00  --inst_lit_activity_flag                true
% 1.72/1.00  --inst_restr_to_given                   false
% 1.72/1.00  --inst_activity_threshold               500
% 1.72/1.00  --inst_out_proof                        true
% 1.72/1.00  
% 1.72/1.00  ------ Resolution Options
% 1.72/1.00  
% 1.72/1.00  --resolution_flag                       false
% 1.72/1.00  --res_lit_sel                           adaptive
% 1.72/1.00  --res_lit_sel_side                      none
% 1.72/1.00  --res_ordering                          kbo
% 1.72/1.00  --res_to_prop_solver                    active
% 1.72/1.00  --res_prop_simpl_new                    false
% 1.72/1.00  --res_prop_simpl_given                  true
% 1.72/1.00  --res_passive_queue_type                priority_queues
% 1.72/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/1.00  --res_passive_queues_freq               [15;5]
% 1.72/1.00  --res_forward_subs                      full
% 1.72/1.00  --res_backward_subs                     full
% 1.72/1.00  --res_forward_subs_resolution           true
% 1.72/1.00  --res_backward_subs_resolution          true
% 1.72/1.00  --res_orphan_elimination                true
% 1.72/1.00  --res_time_limit                        2.
% 1.72/1.00  --res_out_proof                         true
% 1.72/1.00  
% 1.72/1.00  ------ Superposition Options
% 1.72/1.00  
% 1.72/1.00  --superposition_flag                    true
% 1.72/1.00  --sup_passive_queue_type                priority_queues
% 1.72/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.72/1.00  --demod_completeness_check              fast
% 1.72/1.00  --demod_use_ground                      true
% 1.72/1.00  --sup_to_prop_solver                    passive
% 1.72/1.00  --sup_prop_simpl_new                    true
% 1.72/1.00  --sup_prop_simpl_given                  true
% 1.72/1.00  --sup_fun_splitting                     false
% 1.72/1.00  --sup_smt_interval                      50000
% 1.72/1.00  
% 1.72/1.00  ------ Superposition Simplification Setup
% 1.72/1.00  
% 1.72/1.00  --sup_indices_passive                   []
% 1.72/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.00  --sup_full_bw                           [BwDemod]
% 1.72/1.00  --sup_immed_triv                        [TrivRules]
% 1.72/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.00  --sup_immed_bw_main                     []
% 1.72/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.00  
% 1.72/1.00  ------ Combination Options
% 1.72/1.00  
% 1.72/1.00  --comb_res_mult                         3
% 1.72/1.00  --comb_sup_mult                         2
% 1.72/1.00  --comb_inst_mult                        10
% 1.72/1.00  
% 1.72/1.00  ------ Debug Options
% 1.72/1.00  
% 1.72/1.00  --dbg_backtrace                         false
% 1.72/1.00  --dbg_dump_prop_clauses                 false
% 1.72/1.00  --dbg_dump_prop_clauses_file            -
% 1.72/1.00  --dbg_out_stat                          false
% 1.72/1.00  
% 1.72/1.00  
% 1.72/1.00  
% 1.72/1.00  
% 1.72/1.00  ------ Proving...
% 1.72/1.00  
% 1.72/1.00  
% 1.72/1.00  % SZS status Theorem for theBenchmark.p
% 1.72/1.00  
% 1.72/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.72/1.00  
% 1.72/1.00  fof(f11,conjecture,(
% 1.72/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 1.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.00  
% 1.72/1.00  fof(f12,negated_conjecture,(
% 1.72/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 1.72/1.00    inference(negated_conjecture,[],[f11])).
% 1.72/1.00  
% 1.72/1.00  fof(f24,plain,(
% 1.72/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 1.72/1.00    inference(ennf_transformation,[],[f12])).
% 1.72/1.00  
% 1.72/1.00  fof(f25,plain,(
% 1.72/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 1.72/1.00    inference(flattening,[],[f24])).
% 1.72/1.00  
% 1.72/1.00  fof(f30,plain,(
% 1.72/1.00    ( ! [X0,X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X1)) & v1_funct_1(sK2) & v5_relat_1(sK2,X0) & v1_relat_1(sK2))) )),
% 1.72/1.00    introduced(choice_axiom,[])).
% 1.72/1.00  
% 1.72/1.00  fof(f29,plain,(
% 1.72/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK1,X0,X0) & v1_funct_1(sK1))) )),
% 1.72/1.00    introduced(choice_axiom,[])).
% 1.72/1.00  
% 1.72/1.00  fof(f28,plain,(
% 1.72/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) & ~v1_xboole_0(sK0))),
% 1.72/1.00    introduced(choice_axiom,[])).
% 1.72/1.00  
% 1.72/1.00  fof(f31,plain,(
% 1.72/1.00    ((k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)) & ~v1_xboole_0(sK0)),
% 1.72/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30,f29,f28])).
% 1.72/1.00  
% 1.72/1.00  fof(f52,plain,(
% 1.72/1.00    v1_relat_1(sK2)),
% 1.72/1.00    inference(cnf_transformation,[],[f31])).
% 1.72/1.00  
% 1.72/1.00  fof(f5,axiom,(
% 1.72/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.00  
% 1.72/1.00  fof(f37,plain,(
% 1.72/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.72/1.00    inference(cnf_transformation,[],[f5])).
% 1.72/1.00  
% 1.72/1.00  fof(f9,axiom,(
% 1.72/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.00  
% 1.72/1.00  fof(f20,plain,(
% 1.72/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.72/1.00    inference(ennf_transformation,[],[f9])).
% 1.72/1.00  
% 1.72/1.00  fof(f21,plain,(
% 1.72/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.72/1.00    inference(flattening,[],[f20])).
% 1.72/1.00  
% 1.72/1.00  fof(f45,plain,(
% 1.72/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.72/1.00    inference(cnf_transformation,[],[f21])).
% 1.72/1.00  
% 1.72/1.00  fof(f50,plain,(
% 1.72/1.00    v1_funct_2(sK1,sK0,sK0)),
% 1.72/1.00    inference(cnf_transformation,[],[f31])).
% 1.72/1.00  
% 1.72/1.00  fof(f48,plain,(
% 1.72/1.00    ~v1_xboole_0(sK0)),
% 1.72/1.00    inference(cnf_transformation,[],[f31])).
% 1.72/1.00  
% 1.72/1.00  fof(f49,plain,(
% 1.72/1.00    v1_funct_1(sK1)),
% 1.72/1.00    inference(cnf_transformation,[],[f31])).
% 1.72/1.00  
% 1.72/1.00  fof(f51,plain,(
% 1.72/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.72/1.00    inference(cnf_transformation,[],[f31])).
% 1.72/1.00  
% 1.72/1.00  fof(f10,axiom,(
% 1.72/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.00  
% 1.72/1.00  fof(f22,plain,(
% 1.72/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.72/1.00    inference(ennf_transformation,[],[f10])).
% 1.72/1.00  
% 1.72/1.00  fof(f23,plain,(
% 1.72/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.72/1.00    inference(flattening,[],[f22])).
% 1.72/1.00  
% 1.72/1.00  fof(f27,plain,(
% 1.72/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.72/1.00    inference(nnf_transformation,[],[f23])).
% 1.72/1.00  
% 1.72/1.00  fof(f46,plain,(
% 1.72/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.72/1.00    inference(cnf_transformation,[],[f27])).
% 1.72/1.00  
% 1.72/1.00  fof(f8,axiom,(
% 1.72/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.00  
% 1.72/1.00  fof(f19,plain,(
% 1.72/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/1.00    inference(ennf_transformation,[],[f8])).
% 1.72/1.00  
% 1.72/1.00  fof(f42,plain,(
% 1.72/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/1.00    inference(cnf_transformation,[],[f19])).
% 1.72/1.00  
% 1.72/1.00  fof(f3,axiom,(
% 1.72/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.00  
% 1.72/1.00  fof(f35,plain,(
% 1.72/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.72/1.00    inference(cnf_transformation,[],[f3])).
% 1.72/1.00  
% 1.72/1.00  fof(f1,axiom,(
% 1.72/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.00  
% 1.72/1.00  fof(f13,plain,(
% 1.72/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.72/1.00    inference(ennf_transformation,[],[f1])).
% 1.72/1.00  
% 1.72/1.00  fof(f32,plain,(
% 1.72/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.72/1.00    inference(cnf_transformation,[],[f13])).
% 1.72/1.00  
% 1.72/1.00  fof(f4,axiom,(
% 1.72/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 1.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.00  
% 1.72/1.00  fof(f15,plain,(
% 1.72/1.00    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.72/1.00    inference(ennf_transformation,[],[f4])).
% 1.72/1.00  
% 1.72/1.00  fof(f16,plain,(
% 1.72/1.00    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.72/1.00    inference(flattening,[],[f15])).
% 1.72/1.00  
% 1.72/1.00  fof(f36,plain,(
% 1.72/1.00    ( ! [X2,X0,X1] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.72/1.00    inference(cnf_transformation,[],[f16])).
% 1.72/1.00  
% 1.72/1.00  fof(f7,axiom,(
% 1.72/1.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.00  
% 1.72/1.00  fof(f40,plain,(
% 1.72/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.72/1.00    inference(cnf_transformation,[],[f7])).
% 1.72/1.00  
% 1.72/1.00  fof(f2,axiom,(
% 1.72/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.00  
% 1.72/1.00  fof(f14,plain,(
% 1.72/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.72/1.00    inference(ennf_transformation,[],[f2])).
% 1.72/1.00  
% 1.72/1.00  fof(f26,plain,(
% 1.72/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.72/1.00    inference(nnf_transformation,[],[f14])).
% 1.72/1.00  
% 1.72/1.00  fof(f33,plain,(
% 1.72/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.72/1.00    inference(cnf_transformation,[],[f26])).
% 1.72/1.00  
% 1.72/1.00  fof(f6,axiom,(
% 1.72/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/1.00  
% 1.72/1.00  fof(f17,plain,(
% 1.72/1.00    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.72/1.00    inference(ennf_transformation,[],[f6])).
% 1.72/1.00  
% 1.72/1.00  fof(f18,plain,(
% 1.72/1.00    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.72/1.00    inference(flattening,[],[f17])).
% 1.72/1.00  
% 1.72/1.00  fof(f39,plain,(
% 1.72/1.00    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.72/1.00    inference(cnf_transformation,[],[f18])).
% 1.72/1.00  
% 1.72/1.00  fof(f53,plain,(
% 1.72/1.00    v5_relat_1(sK2,sK0)),
% 1.72/1.00    inference(cnf_transformation,[],[f31])).
% 1.72/1.00  
% 1.72/1.00  fof(f55,plain,(
% 1.72/1.00    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))),
% 1.72/1.00    inference(cnf_transformation,[],[f31])).
% 1.72/1.00  
% 1.72/1.00  cnf(c_19,negated_conjecture,
% 1.72/1.00      ( v1_relat_1(sK2) ),
% 1.72/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_610,plain,
% 1.72/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 1.72/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_6,plain,
% 1.72/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 1.72/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_12,plain,
% 1.72/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.72/1.00      | v1_partfun1(X0,X1)
% 1.72/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.00      | v1_xboole_0(X2)
% 1.72/1.00      | ~ v1_funct_1(X0) ),
% 1.72/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_21,negated_conjecture,
% 1.72/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 1.72/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_232,plain,
% 1.72/1.00      ( v1_partfun1(X0,X1)
% 1.72/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.00      | v1_xboole_0(X2)
% 1.72/1.00      | ~ v1_funct_1(X0)
% 1.72/1.00      | sK0 != X2
% 1.72/1.00      | sK0 != X1
% 1.72/1.00      | sK1 != X0 ),
% 1.72/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_233,plain,
% 1.72/1.00      ( v1_partfun1(sK1,sK0)
% 1.72/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.72/1.00      | v1_xboole_0(sK0)
% 1.72/1.00      | ~ v1_funct_1(sK1) ),
% 1.72/1.00      inference(unflattening,[status(thm)],[c_232]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_23,negated_conjecture,
% 1.72/1.00      ( ~ v1_xboole_0(sK0) ),
% 1.72/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_22,negated_conjecture,
% 1.72/1.00      ( v1_funct_1(sK1) ),
% 1.72/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_20,negated_conjecture,
% 1.72/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.72/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_235,plain,
% 1.72/1.00      ( v1_partfun1(sK1,sK0) ),
% 1.72/1.00      inference(global_propositional_subsumption,
% 1.72/1.00                [status(thm)],
% 1.72/1.00                [c_233,c_23,c_22,c_20]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_15,plain,
% 1.72/1.00      ( ~ v1_partfun1(X0,X1)
% 1.72/1.00      | ~ v4_relat_1(X0,X1)
% 1.72/1.00      | ~ v1_relat_1(X0)
% 1.72/1.00      | k1_relat_1(X0) = X1 ),
% 1.72/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_11,plain,
% 1.72/1.00      ( v4_relat_1(X0,X1)
% 1.72/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.72/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_272,plain,
% 1.72/1.00      ( v4_relat_1(X0,X1)
% 1.72/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.72/1.00      | sK1 != X0 ),
% 1.72/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_273,plain,
% 1.72/1.00      ( v4_relat_1(sK1,X0)
% 1.72/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.72/1.00      inference(unflattening,[status(thm)],[c_272]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_294,plain,
% 1.72/1.00      ( ~ v1_partfun1(X0,X1)
% 1.72/1.00      | ~ v1_relat_1(X0)
% 1.72/1.00      | X2 != X1
% 1.72/1.00      | k1_relat_1(X0) = X1
% 1.72/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.72/1.00      | sK1 != X0 ),
% 1.72/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_273]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_295,plain,
% 1.72/1.00      ( ~ v1_partfun1(sK1,X0)
% 1.72/1.00      | ~ v1_relat_1(sK1)
% 1.72/1.00      | k1_relat_1(sK1) = X0
% 1.72/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.72/1.00      inference(unflattening,[status(thm)],[c_294]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_383,plain,
% 1.72/1.00      ( ~ v1_relat_1(sK1)
% 1.72/1.00      | k1_relat_1(sK1) = X0
% 1.72/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.72/1.00      | sK0 != X0
% 1.72/1.00      | sK1 != sK1 ),
% 1.72/1.00      inference(resolution_lifted,[status(thm)],[c_235,c_295]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_384,plain,
% 1.72/1.00      ( ~ v1_relat_1(sK1)
% 1.72/1.00      | k1_relat_1(sK1) = sK0
% 1.72/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 1.72/1.00      inference(unflattening,[status(thm)],[c_383]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_457,plain,
% 1.72/1.00      ( ~ v1_relat_1(sK1) | sP0_iProver_split | k1_relat_1(sK1) = sK0 ),
% 1.72/1.00      inference(splitting,
% 1.72/1.00                [splitting(split),new_symbols(definition,[])],
% 1.72/1.00                [c_384]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_606,plain,
% 1.72/1.00      ( k1_relat_1(sK1) = sK0
% 1.72/1.00      | v1_relat_1(sK1) != iProver_top
% 1.72/1.00      | sP0_iProver_split = iProver_top ),
% 1.72/1.00      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_3,plain,
% 1.72/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.72/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_61,plain,
% 1.72/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 1.72/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_63,plain,
% 1.72/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 1.72/1.00      inference(instantiation,[status(thm)],[c_61]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_477,plain,
% 1.72/1.00      ( k1_relat_1(sK1) = sK0
% 1.72/1.00      | v1_relat_1(sK1) != iProver_top
% 1.72/1.00      | sP0_iProver_split = iProver_top ),
% 1.72/1.00      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_0,plain,
% 1.72/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.72/1.00      | ~ v1_relat_1(X1)
% 1.72/1.00      | v1_relat_1(X0) ),
% 1.72/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_245,plain,
% 1.72/1.00      ( ~ v1_relat_1(X0)
% 1.72/1.00      | v1_relat_1(X1)
% 1.72/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(X0)
% 1.72/1.00      | sK1 != X1 ),
% 1.72/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_246,plain,
% 1.72/1.00      ( ~ v1_relat_1(X0)
% 1.72/1.00      | v1_relat_1(sK1)
% 1.72/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(X0) ),
% 1.72/1.00      inference(unflattening,[status(thm)],[c_245]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_609,plain,
% 1.72/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(X0)
% 1.72/1.00      | v1_relat_1(X0) != iProver_top
% 1.72/1.00      | v1_relat_1(sK1) = iProver_top ),
% 1.72/1.00      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_716,plain,
% 1.72/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 1.72/1.00      | v1_relat_1(sK1) = iProver_top ),
% 1.72/1.00      inference(equality_resolution,[status(thm)],[c_609]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_456,plain,
% 1.72/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.72/1.00      | ~ sP0_iProver_split ),
% 1.72/1.00      inference(splitting,
% 1.72/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.72/1.00                [c_384]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_607,plain,
% 1.72/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 1.72/1.00      | sP0_iProver_split != iProver_top ),
% 1.72/1.00      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_840,plain,
% 1.72/1.00      ( sP0_iProver_split != iProver_top ),
% 1.72/1.00      inference(equality_resolution,[status(thm)],[c_607]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_930,plain,
% 1.72/1.00      ( k1_relat_1(sK1) = sK0 ),
% 1.72/1.00      inference(global_propositional_subsumption,
% 1.72/1.00                [status(thm)],
% 1.72/1.00                [c_606,c_63,c_477,c_716,c_840]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_4,plain,
% 1.72/1.00      ( ~ v1_relat_1(X0)
% 1.72/1.00      | ~ v1_relat_1(X1)
% 1.72/1.00      | ~ v1_relat_1(X2)
% 1.72/1.00      | k1_relat_1(X1) != k1_relat_1(X0)
% 1.72/1.00      | k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(k5_relat_1(X2,X0)) ),
% 1.72/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_612,plain,
% 1.72/1.00      ( k1_relat_1(X0) != k1_relat_1(X1)
% 1.72/1.00      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
% 1.72/1.00      | v1_relat_1(X1) != iProver_top
% 1.72/1.00      | v1_relat_1(X0) != iProver_top
% 1.72/1.00      | v1_relat_1(X2) != iProver_top ),
% 1.72/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_1610,plain,
% 1.72/1.00      ( k1_relat_1(X0) != sK0
% 1.72/1.00      | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(k5_relat_1(X1,sK1))
% 1.72/1.00      | v1_relat_1(X0) != iProver_top
% 1.72/1.00      | v1_relat_1(X1) != iProver_top
% 1.72/1.00      | v1_relat_1(sK1) != iProver_top ),
% 1.72/1.00      inference(superposition,[status(thm)],[c_930,c_612]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_1753,plain,
% 1.72/1.00      ( v1_relat_1(X1) != iProver_top
% 1.72/1.00      | v1_relat_1(X0) != iProver_top
% 1.72/1.00      | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(k5_relat_1(X1,sK1))
% 1.72/1.00      | k1_relat_1(X0) != sK0 ),
% 1.72/1.00      inference(global_propositional_subsumption,
% 1.72/1.00                [status(thm)],
% 1.72/1.00                [c_1610,c_63,c_716]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_1754,plain,
% 1.72/1.00      ( k1_relat_1(X0) != sK0
% 1.72/1.00      | k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(k5_relat_1(X1,sK1))
% 1.72/1.00      | v1_relat_1(X0) != iProver_top
% 1.72/1.00      | v1_relat_1(X1) != iProver_top ),
% 1.72/1.00      inference(renaming,[status(thm)],[c_1753]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_1763,plain,
% 1.72/1.00      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X0,sK1))
% 1.72/1.00      | sK0 != X1
% 1.72/1.00      | v1_relat_1(X0) != iProver_top
% 1.72/1.00      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 1.72/1.00      inference(superposition,[status(thm)],[c_6,c_1754]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_9,plain,
% 1.72/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 1.72/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_611,plain,
% 1.72/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 1.72/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_1803,plain,
% 1.72/1.00      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X0,sK1))
% 1.72/1.00      | sK0 != X1
% 1.72/1.00      | v1_relat_1(X0) != iProver_top ),
% 1.72/1.00      inference(forward_subsumption_resolution,
% 1.72/1.00                [status(thm)],
% 1.72/1.00                [c_1763,c_611]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_1807,plain,
% 1.72/1.00      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(sK0))) = k1_relat_1(k5_relat_1(X0,sK1))
% 1.72/1.00      | v1_relat_1(X0) != iProver_top ),
% 1.72/1.00      inference(equality_resolution,[status(thm)],[c_1803]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_1816,plain,
% 1.72/1.00      ( k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK0))) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
% 1.72/1.00      inference(superposition,[status(thm)],[c_610,c_1807]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_2,plain,
% 1.72/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 1.72/1.00      | ~ v5_relat_1(X0,X1)
% 1.72/1.00      | ~ v1_relat_1(X0) ),
% 1.72/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_7,plain,
% 1.72/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 1.72/1.00      | ~ v1_relat_1(X0)
% 1.72/1.00      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 1.72/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_336,plain,
% 1.72/1.00      ( ~ v5_relat_1(X0,X1)
% 1.72/1.00      | ~ v1_relat_1(X0)
% 1.72/1.00      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 1.72/1.00      inference(resolution,[status(thm)],[c_2,c_7]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_18,negated_conjecture,
% 1.72/1.00      ( v5_relat_1(sK2,sK0) ),
% 1.72/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_355,plain,
% 1.72/1.00      ( ~ v1_relat_1(X0)
% 1.72/1.00      | k5_relat_1(X0,k6_relat_1(X1)) = X0
% 1.72/1.00      | sK0 != X1
% 1.72/1.00      | sK2 != X0 ),
% 1.72/1.00      inference(resolution_lifted,[status(thm)],[c_336,c_18]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_356,plain,
% 1.72/1.00      ( ~ v1_relat_1(sK2) | k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 1.72/1.00      inference(unflattening,[status(thm)],[c_355]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_358,plain,
% 1.72/1.00      ( k5_relat_1(sK2,k6_relat_1(sK0)) = sK2 ),
% 1.72/1.00      inference(global_propositional_subsumption,
% 1.72/1.00                [status(thm)],
% 1.72/1.00                [c_356,c_19]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_1822,plain,
% 1.72/1.00      ( k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(sK2) ),
% 1.72/1.00      inference(light_normalisation,[status(thm)],[c_1816,c_358]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_459,plain,( X0 = X0 ),theory(equality) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_918,plain,
% 1.72/1.00      ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
% 1.72/1.00      inference(instantiation,[status(thm)],[c_459]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_460,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_709,plain,
% 1.72/1.00      ( k1_relat_1(k5_relat_1(sK2,sK1)) != X0
% 1.72/1.00      | k1_relat_1(sK2) != X0
% 1.72/1.00      | k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
% 1.72/1.00      inference(instantiation,[status(thm)],[c_460]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_760,plain,
% 1.72/1.00      ( k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(X0)
% 1.72/1.00      | k1_relat_1(sK2) != k1_relat_1(X0)
% 1.72/1.00      | k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
% 1.72/1.00      inference(instantiation,[status(thm)],[c_709]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_917,plain,
% 1.72/1.00      ( k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2)
% 1.72/1.00      | k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1))
% 1.72/1.00      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 1.72/1.00      inference(instantiation,[status(thm)],[c_760]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(c_16,negated_conjecture,
% 1.72/1.00      ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
% 1.72/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.72/1.00  
% 1.72/1.00  cnf(contradiction,plain,
% 1.72/1.00      ( $false ),
% 1.72/1.00      inference(minisat,[status(thm)],[c_1822,c_918,c_917,c_16]) ).
% 1.72/1.00  
% 1.72/1.00  
% 1.72/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.72/1.00  
% 1.72/1.00  ------                               Statistics
% 1.72/1.00  
% 1.72/1.00  ------ General
% 1.72/1.00  
% 1.72/1.00  abstr_ref_over_cycles:                  0
% 1.72/1.00  abstr_ref_under_cycles:                 0
% 1.72/1.00  gc_basic_clause_elim:                   0
% 1.72/1.00  forced_gc_time:                         0
% 1.72/1.00  parsing_time:                           0.008
% 1.72/1.00  unif_index_cands_time:                  0.
% 1.72/1.00  unif_index_add_time:                    0.
% 1.72/1.00  orderings_time:                         0.
% 1.72/1.00  out_proof_time:                         0.011
% 1.72/1.00  total_time:                             0.105
% 1.72/1.00  num_of_symbols:                         50
% 1.72/1.00  num_of_terms:                           1953
% 1.72/1.00  
% 1.72/1.00  ------ Preprocessing
% 1.72/1.00  
% 1.72/1.00  num_of_splits:                          1
% 1.72/1.00  num_of_split_atoms:                     1
% 1.72/1.00  num_of_reused_defs:                     0
% 1.72/1.00  num_eq_ax_congr_red:                    4
% 1.72/1.00  num_of_sem_filtered_clauses:            1
% 1.72/1.00  num_of_subtypes:                        0
% 1.72/1.00  monotx_restored_types:                  0
% 1.72/1.00  sat_num_of_epr_types:                   0
% 1.72/1.00  sat_num_of_non_cyclic_types:            0
% 1.72/1.00  sat_guarded_non_collapsed_types:        0
% 1.72/1.00  num_pure_diseq_elim:                    0
% 1.72/1.00  simp_replaced_by:                       0
% 1.72/1.00  res_preprocessed:                       77
% 1.72/1.00  prep_upred:                             0
% 1.72/1.00  prep_unflattend:                        16
% 1.72/1.00  smt_new_axioms:                         0
% 1.72/1.00  pred_elim_cands:                        1
% 1.72/1.00  pred_elim:                              8
% 1.72/1.00  pred_elim_cl:                           12
% 1.72/1.00  pred_elim_cycles:                       10
% 1.72/1.00  merged_defs:                            0
% 1.72/1.00  merged_defs_ncl:                        0
% 1.72/1.00  bin_hyper_res:                          0
% 1.72/1.00  prep_cycles:                            4
% 1.72/1.00  pred_elim_time:                         0.003
% 1.72/1.00  splitting_time:                         0.
% 1.72/1.00  sem_filter_time:                        0.
% 1.72/1.00  monotx_time:                            0.001
% 1.72/1.00  subtype_inf_time:                       0.
% 1.72/1.00  
% 1.72/1.00  ------ Problem properties
% 1.72/1.00  
% 1.72/1.00  clauses:                                12
% 1.72/1.00  conjectures:                            2
% 1.72/1.00  epr:                                    1
% 1.72/1.00  horn:                                   11
% 1.72/1.00  ground:                                 4
% 1.72/1.00  unary:                                  7
% 1.72/1.00  binary:                                 1
% 1.72/1.00  lits:                                   23
% 1.72/1.00  lits_eq:                                11
% 1.72/1.00  fd_pure:                                0
% 1.72/1.00  fd_pseudo:                              0
% 1.72/1.00  fd_cond:                                0
% 1.72/1.00  fd_pseudo_cond:                         0
% 1.72/1.00  ac_symbols:                             0
% 1.72/1.00  
% 1.72/1.00  ------ Propositional Solver
% 1.72/1.00  
% 1.72/1.00  prop_solver_calls:                      26
% 1.72/1.00  prop_fast_solver_calls:                 392
% 1.72/1.00  smt_solver_calls:                       0
% 1.72/1.00  smt_fast_solver_calls:                  0
% 1.72/1.00  prop_num_of_clauses:                    791
% 1.72/1.00  prop_preprocess_simplified:             2865
% 1.72/1.00  prop_fo_subsumed:                       9
% 1.72/1.00  prop_solver_time:                       0.
% 1.72/1.00  smt_solver_time:                        0.
% 1.72/1.00  smt_fast_solver_time:                   0.
% 1.72/1.00  prop_fast_solver_time:                  0.
% 1.72/1.00  prop_unsat_core_time:                   0.
% 1.72/1.00  
% 1.72/1.00  ------ QBF
% 1.72/1.00  
% 1.72/1.00  qbf_q_res:                              0
% 1.72/1.00  qbf_num_tautologies:                    0
% 1.72/1.00  qbf_prep_cycles:                        0
% 1.72/1.00  
% 1.72/1.00  ------ BMC1
% 1.72/1.00  
% 1.72/1.00  bmc1_current_bound:                     -1
% 1.72/1.00  bmc1_last_solved_bound:                 -1
% 1.72/1.00  bmc1_unsat_core_size:                   -1
% 1.72/1.00  bmc1_unsat_core_parents_size:           -1
% 1.72/1.00  bmc1_merge_next_fun:                    0
% 1.72/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.72/1.00  
% 1.72/1.00  ------ Instantiation
% 1.72/1.00  
% 1.72/1.00  inst_num_of_clauses:                    239
% 1.72/1.00  inst_num_in_passive:                    115
% 1.72/1.00  inst_num_in_active:                     87
% 1.72/1.00  inst_num_in_unprocessed:                38
% 1.72/1.00  inst_num_of_loops:                      90
% 1.72/1.00  inst_num_of_learning_restarts:          0
% 1.72/1.00  inst_num_moves_active_passive:          2
% 1.72/1.00  inst_lit_activity:                      0
% 1.72/1.00  inst_lit_activity_moves:                0
% 1.72/1.00  inst_num_tautologies:                   0
% 1.72/1.00  inst_num_prop_implied:                  0
% 1.72/1.00  inst_num_existing_simplified:           0
% 1.72/1.00  inst_num_eq_res_simplified:             0
% 1.72/1.00  inst_num_child_elim:                    0
% 1.72/1.00  inst_num_of_dismatching_blockings:      6
% 1.72/1.00  inst_num_of_non_proper_insts:           186
% 1.72/1.00  inst_num_of_duplicates:                 0
% 1.72/1.00  inst_inst_num_from_inst_to_res:         0
% 1.72/1.00  inst_dismatching_checking_time:         0.
% 1.72/1.00  
% 1.72/1.00  ------ Resolution
% 1.72/1.00  
% 1.72/1.00  res_num_of_clauses:                     0
% 1.72/1.00  res_num_in_passive:                     0
% 1.72/1.00  res_num_in_active:                      0
% 1.72/1.00  res_num_of_loops:                       81
% 1.72/1.00  res_forward_subset_subsumed:            6
% 1.72/1.00  res_backward_subset_subsumed:           2
% 1.72/1.00  res_forward_subsumed:                   0
% 1.72/1.00  res_backward_subsumed:                  0
% 1.72/1.00  res_forward_subsumption_resolution:     0
% 1.72/1.00  res_backward_subsumption_resolution:    0
% 1.72/1.00  res_clause_to_clause_subsumption:       23
% 1.72/1.00  res_orphan_elimination:                 0
% 1.72/1.00  res_tautology_del:                      11
% 1.72/1.00  res_num_eq_res_simplified:              0
% 1.72/1.00  res_num_sel_changes:                    0
% 1.72/1.00  res_moves_from_active_to_pass:          0
% 1.72/1.00  
% 1.72/1.00  ------ Superposition
% 1.72/1.00  
% 1.72/1.00  sup_time_total:                         0.
% 1.72/1.00  sup_time_generating:                    0.
% 1.72/1.00  sup_time_sim_full:                      0.
% 1.72/1.00  sup_time_sim_immed:                     0.
% 1.72/1.00  
% 1.72/1.00  sup_num_of_clauses:                     23
% 1.72/1.00  sup_num_in_active:                      18
% 1.72/1.00  sup_num_in_passive:                     5
% 1.72/1.00  sup_num_of_loops:                       17
% 1.72/1.00  sup_fw_superposition:                   10
% 1.72/1.00  sup_bw_superposition:                   0
% 1.72/1.00  sup_immediate_simplified:               2
% 1.72/1.00  sup_given_eliminated:                   0
% 1.72/1.00  comparisons_done:                       0
% 1.72/1.00  comparisons_avoided:                    0
% 1.72/1.00  
% 1.72/1.00  ------ Simplifications
% 1.72/1.00  
% 1.72/1.00  
% 1.72/1.00  sim_fw_subset_subsumed:                 0
% 1.72/1.00  sim_bw_subset_subsumed:                 0
% 1.72/1.00  sim_fw_subsumed:                        0
% 1.72/1.00  sim_bw_subsumed:                        0
% 1.72/1.00  sim_fw_subsumption_res:                 1
% 1.72/1.00  sim_bw_subsumption_res:                 0
% 1.72/1.00  sim_tautology_del:                      0
% 1.72/1.00  sim_eq_tautology_del:                   2
% 1.72/1.00  sim_eq_res_simp:                        0
% 1.72/1.00  sim_fw_demodulated:                     0
% 1.72/1.00  sim_bw_demodulated:                     0
% 1.72/1.00  sim_light_normalised:                   2
% 1.72/1.00  sim_joinable_taut:                      0
% 1.72/1.00  sim_joinable_simp:                      0
% 1.72/1.00  sim_ac_normalised:                      0
% 1.72/1.00  sim_smt_subsumption:                    0
% 1.72/1.00  
%------------------------------------------------------------------------------
