%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:28 EST 2020

% Result     : Theorem 1.21s
% Output     : CNFRefutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 373 expanded)
%              Number of clauses        :   68 ( 147 expanded)
%              Number of leaves         :   18 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  309 (1171 expanded)
%              Number of equality atoms :  110 ( 287 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f23])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK2,X2),k8_setfam_1(sK2,sK3))
          & r1_tarski(sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f33,f32])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f36,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f29])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f45])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_791,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_800,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2064,plain,
    ( k6_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_791,c_800])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_798,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1715,plain,
    ( k6_setfam_1(sK2,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_791,c_798])).

cnf(c_2067,plain,
    ( k8_setfam_1(sK2,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2064,c_1715])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_48,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_322,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1040,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_1041,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1044,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_321,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1062,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_157,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_188,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_157])).

cnf(c_1150,plain,
    ( ~ r1_tarski(sK3,X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_1152,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_328,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_967,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK3,sK4)
    | X0 != sK3
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_1157,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,sK4)
    | X0 != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1160,plain,
    ( ~ r1_tarski(sK3,sK4)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1046,plain,
    ( r1_tarski(k1_setfam_1(X0),k1_setfam_1(sK3))
    | ~ r1_tarski(sK3,X0)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1213,plain,
    ( r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3))
    | ~ r1_tarski(sK3,sK4)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_1339,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3))
    | X1 != k1_setfam_1(sK3)
    | X0 != k1_setfam_1(sK4) ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_1550,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    | ~ r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3))
    | k8_setfam_1(sK2,sK3) != k1_setfam_1(sK3)
    | k8_setfam_1(sK2,sK4) != k1_setfam_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_1232,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_1934,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_1935,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_792,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2063,plain,
    ( k6_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_792,c_800])).

cnf(c_1714,plain,
    ( k6_setfam_1(sK2,sK4) = k1_setfam_1(sK4) ),
    inference(superposition,[status(thm)],[c_792,c_798])).

cnf(c_2072,plain,
    ( k8_setfam_1(sK2,sK4) = k1_setfam_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2063,c_1714])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_809,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_802,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_806,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2277,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_802,c_806])).

cnf(c_2286,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_2277])).

cnf(c_2295,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2286])).

cnf(c_2459,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2067,c_17,c_16,c_7,c_48,c_1041,c_1044,c_1062,c_1152,c_1160,c_1213,c_1550,c_1935,c_2072,c_2295])).

cnf(c_2469,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2459,c_791])).

cnf(c_9,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_801,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2559,plain,
    ( k8_setfam_1(sK2,k1_xboole_0) = sK2 ),
    inference(superposition,[status(thm)],[c_2469,c_801])).

cnf(c_794,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2468,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2459,c_794])).

cnf(c_2637,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2559,c_2468])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_999,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),sK2)
    | ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1000,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),sK2) = iProver_top
    | m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_999])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_941,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_942,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_941])).

cnf(c_21,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2637,c_1000,c_942,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:53:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.21/1.10  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.21/1.10  
% 1.21/1.10  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.21/1.10  
% 1.21/1.10  ------  iProver source info
% 1.21/1.10  
% 1.21/1.10  git: date: 2020-06-30 10:37:57 +0100
% 1.21/1.10  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.21/1.10  git: non_committed_changes: false
% 1.21/1.10  git: last_make_outside_of_git: false
% 1.21/1.10  
% 1.21/1.10  ------ 
% 1.21/1.10  
% 1.21/1.10  ------ Input Options
% 1.21/1.10  
% 1.21/1.10  --out_options                           all
% 1.21/1.10  --tptp_safe_out                         true
% 1.21/1.10  --problem_path                          ""
% 1.21/1.10  --include_path                          ""
% 1.21/1.10  --clausifier                            res/vclausify_rel
% 1.21/1.10  --clausifier_options                    --mode clausify
% 1.21/1.10  --stdin                                 false
% 1.21/1.10  --stats_out                             all
% 1.21/1.10  
% 1.21/1.10  ------ General Options
% 1.21/1.10  
% 1.21/1.10  --fof                                   false
% 1.21/1.10  --time_out_real                         305.
% 1.21/1.10  --time_out_virtual                      -1.
% 1.21/1.10  --symbol_type_check                     false
% 1.21/1.10  --clausify_out                          false
% 1.21/1.10  --sig_cnt_out                           false
% 1.21/1.10  --trig_cnt_out                          false
% 1.21/1.10  --trig_cnt_out_tolerance                1.
% 1.21/1.10  --trig_cnt_out_sk_spl                   false
% 1.21/1.10  --abstr_cl_out                          false
% 1.21/1.10  
% 1.21/1.10  ------ Global Options
% 1.21/1.10  
% 1.21/1.10  --schedule                              default
% 1.21/1.10  --add_important_lit                     false
% 1.21/1.10  --prop_solver_per_cl                    1000
% 1.21/1.10  --min_unsat_core                        false
% 1.21/1.10  --soft_assumptions                      false
% 1.21/1.10  --soft_lemma_size                       3
% 1.21/1.10  --prop_impl_unit_size                   0
% 1.21/1.10  --prop_impl_unit                        []
% 1.21/1.10  --share_sel_clauses                     true
% 1.21/1.10  --reset_solvers                         false
% 1.21/1.10  --bc_imp_inh                            [conj_cone]
% 1.21/1.10  --conj_cone_tolerance                   3.
% 1.21/1.10  --extra_neg_conj                        none
% 1.21/1.10  --large_theory_mode                     true
% 1.21/1.10  --prolific_symb_bound                   200
% 1.21/1.10  --lt_threshold                          2000
% 1.21/1.10  --clause_weak_htbl                      true
% 1.21/1.10  --gc_record_bc_elim                     false
% 1.21/1.10  
% 1.21/1.10  ------ Preprocessing Options
% 1.21/1.10  
% 1.21/1.10  --preprocessing_flag                    true
% 1.21/1.10  --time_out_prep_mult                    0.1
% 1.21/1.10  --splitting_mode                        input
% 1.21/1.10  --splitting_grd                         true
% 1.21/1.10  --splitting_cvd                         false
% 1.21/1.10  --splitting_cvd_svl                     false
% 1.21/1.10  --splitting_nvd                         32
% 1.21/1.10  --sub_typing                            true
% 1.21/1.10  --prep_gs_sim                           true
% 1.21/1.10  --prep_unflatten                        true
% 1.21/1.10  --prep_res_sim                          true
% 1.21/1.10  --prep_upred                            true
% 1.21/1.10  --prep_sem_filter                       exhaustive
% 1.21/1.10  --prep_sem_filter_out                   false
% 1.21/1.10  --pred_elim                             true
% 1.21/1.10  --res_sim_input                         true
% 1.21/1.10  --eq_ax_congr_red                       true
% 1.21/1.10  --pure_diseq_elim                       true
% 1.21/1.10  --brand_transform                       false
% 1.21/1.10  --non_eq_to_eq                          false
% 1.21/1.10  --prep_def_merge                        true
% 1.21/1.10  --prep_def_merge_prop_impl              false
% 1.21/1.10  --prep_def_merge_mbd                    true
% 1.21/1.10  --prep_def_merge_tr_red                 false
% 1.21/1.10  --prep_def_merge_tr_cl                  false
% 1.21/1.10  --smt_preprocessing                     true
% 1.21/1.10  --smt_ac_axioms                         fast
% 1.21/1.10  --preprocessed_out                      false
% 1.21/1.10  --preprocessed_stats                    false
% 1.21/1.10  
% 1.21/1.10  ------ Abstraction refinement Options
% 1.21/1.10  
% 1.21/1.10  --abstr_ref                             []
% 1.21/1.10  --abstr_ref_prep                        false
% 1.21/1.10  --abstr_ref_until_sat                   false
% 1.21/1.10  --abstr_ref_sig_restrict                funpre
% 1.21/1.10  --abstr_ref_af_restrict_to_split_sk     false
% 1.21/1.10  --abstr_ref_under                       []
% 1.21/1.10  
% 1.21/1.10  ------ SAT Options
% 1.21/1.10  
% 1.21/1.10  --sat_mode                              false
% 1.21/1.10  --sat_fm_restart_options                ""
% 1.21/1.10  --sat_gr_def                            false
% 1.21/1.10  --sat_epr_types                         true
% 1.21/1.10  --sat_non_cyclic_types                  false
% 1.21/1.10  --sat_finite_models                     false
% 1.21/1.10  --sat_fm_lemmas                         false
% 1.21/1.10  --sat_fm_prep                           false
% 1.21/1.10  --sat_fm_uc_incr                        true
% 1.21/1.10  --sat_out_model                         small
% 1.21/1.10  --sat_out_clauses                       false
% 1.21/1.10  
% 1.21/1.10  ------ QBF Options
% 1.21/1.10  
% 1.21/1.10  --qbf_mode                              false
% 1.21/1.10  --qbf_elim_univ                         false
% 1.21/1.10  --qbf_dom_inst                          none
% 1.21/1.10  --qbf_dom_pre_inst                      false
% 1.21/1.10  --qbf_sk_in                             false
% 1.21/1.10  --qbf_pred_elim                         true
% 1.21/1.10  --qbf_split                             512
% 1.21/1.10  
% 1.21/1.10  ------ BMC1 Options
% 1.21/1.10  
% 1.21/1.10  --bmc1_incremental                      false
% 1.21/1.10  --bmc1_axioms                           reachable_all
% 1.21/1.10  --bmc1_min_bound                        0
% 1.21/1.10  --bmc1_max_bound                        -1
% 1.21/1.10  --bmc1_max_bound_default                -1
% 1.21/1.10  --bmc1_symbol_reachability              true
% 1.21/1.10  --bmc1_property_lemmas                  false
% 1.21/1.10  --bmc1_k_induction                      false
% 1.21/1.10  --bmc1_non_equiv_states                 false
% 1.21/1.10  --bmc1_deadlock                         false
% 1.21/1.10  --bmc1_ucm                              false
% 1.21/1.10  --bmc1_add_unsat_core                   none
% 1.21/1.10  --bmc1_unsat_core_children              false
% 1.21/1.10  --bmc1_unsat_core_extrapolate_axioms    false
% 1.21/1.10  --bmc1_out_stat                         full
% 1.21/1.10  --bmc1_ground_init                      false
% 1.21/1.10  --bmc1_pre_inst_next_state              false
% 1.21/1.10  --bmc1_pre_inst_state                   false
% 1.21/1.10  --bmc1_pre_inst_reach_state             false
% 1.21/1.10  --bmc1_out_unsat_core                   false
% 1.21/1.10  --bmc1_aig_witness_out                  false
% 1.21/1.10  --bmc1_verbose                          false
% 1.21/1.10  --bmc1_dump_clauses_tptp                false
% 1.21/1.10  --bmc1_dump_unsat_core_tptp             false
% 1.21/1.10  --bmc1_dump_file                        -
% 1.21/1.10  --bmc1_ucm_expand_uc_limit              128
% 1.21/1.10  --bmc1_ucm_n_expand_iterations          6
% 1.21/1.10  --bmc1_ucm_extend_mode                  1
% 1.21/1.10  --bmc1_ucm_init_mode                    2
% 1.21/1.10  --bmc1_ucm_cone_mode                    none
% 1.21/1.10  --bmc1_ucm_reduced_relation_type        0
% 1.21/1.10  --bmc1_ucm_relax_model                  4
% 1.21/1.10  --bmc1_ucm_full_tr_after_sat            true
% 1.21/1.10  --bmc1_ucm_expand_neg_assumptions       false
% 1.21/1.10  --bmc1_ucm_layered_model                none
% 1.21/1.10  --bmc1_ucm_max_lemma_size               10
% 1.21/1.10  
% 1.21/1.10  ------ AIG Options
% 1.21/1.10  
% 1.21/1.10  --aig_mode                              false
% 1.21/1.10  
% 1.21/1.10  ------ Instantiation Options
% 1.21/1.10  
% 1.21/1.10  --instantiation_flag                    true
% 1.21/1.10  --inst_sos_flag                         false
% 1.21/1.10  --inst_sos_phase                        true
% 1.21/1.10  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.21/1.10  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.21/1.10  --inst_lit_sel_side                     num_symb
% 1.21/1.10  --inst_solver_per_active                1400
% 1.21/1.10  --inst_solver_calls_frac                1.
% 1.21/1.10  --inst_passive_queue_type               priority_queues
% 1.21/1.10  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.21/1.10  --inst_passive_queues_freq              [25;2]
% 1.21/1.10  --inst_dismatching                      true
% 1.21/1.10  --inst_eager_unprocessed_to_passive     true
% 1.21/1.10  --inst_prop_sim_given                   true
% 1.21/1.10  --inst_prop_sim_new                     false
% 1.21/1.10  --inst_subs_new                         false
% 1.21/1.10  --inst_eq_res_simp                      false
% 1.21/1.10  --inst_subs_given                       false
% 1.21/1.10  --inst_orphan_elimination               true
% 1.21/1.10  --inst_learning_loop_flag               true
% 1.21/1.10  --inst_learning_start                   3000
% 1.21/1.10  --inst_learning_factor                  2
% 1.21/1.10  --inst_start_prop_sim_after_learn       3
% 1.21/1.10  --inst_sel_renew                        solver
% 1.21/1.10  --inst_lit_activity_flag                true
% 1.21/1.10  --inst_restr_to_given                   false
% 1.21/1.10  --inst_activity_threshold               500
% 1.21/1.10  --inst_out_proof                        true
% 1.21/1.10  
% 1.21/1.10  ------ Resolution Options
% 1.21/1.10  
% 1.21/1.10  --resolution_flag                       true
% 1.21/1.10  --res_lit_sel                           adaptive
% 1.21/1.10  --res_lit_sel_side                      none
% 1.21/1.10  --res_ordering                          kbo
% 1.21/1.10  --res_to_prop_solver                    active
% 1.21/1.10  --res_prop_simpl_new                    false
% 1.21/1.10  --res_prop_simpl_given                  true
% 1.21/1.10  --res_passive_queue_type                priority_queues
% 1.21/1.10  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.21/1.10  --res_passive_queues_freq               [15;5]
% 1.21/1.10  --res_forward_subs                      full
% 1.21/1.10  --res_backward_subs                     full
% 1.21/1.10  --res_forward_subs_resolution           true
% 1.21/1.10  --res_backward_subs_resolution          true
% 1.21/1.10  --res_orphan_elimination                true
% 1.21/1.10  --res_time_limit                        2.
% 1.21/1.10  --res_out_proof                         true
% 1.21/1.10  
% 1.21/1.10  ------ Superposition Options
% 1.21/1.10  
% 1.21/1.10  --superposition_flag                    true
% 1.21/1.10  --sup_passive_queue_type                priority_queues
% 1.21/1.10  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.21/1.10  --sup_passive_queues_freq               [8;1;4]
% 1.21/1.10  --demod_completeness_check              fast
% 1.21/1.10  --demod_use_ground                      true
% 1.21/1.10  --sup_to_prop_solver                    passive
% 1.21/1.10  --sup_prop_simpl_new                    true
% 1.21/1.10  --sup_prop_simpl_given                  true
% 1.21/1.10  --sup_fun_splitting                     false
% 1.21/1.10  --sup_smt_interval                      50000
% 1.21/1.10  
% 1.21/1.10  ------ Superposition Simplification Setup
% 1.21/1.10  
% 1.21/1.10  --sup_indices_passive                   []
% 1.21/1.10  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.10  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.10  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.10  --sup_full_triv                         [TrivRules;PropSubs]
% 1.21/1.10  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.10  --sup_full_bw                           [BwDemod]
% 1.21/1.10  --sup_immed_triv                        [TrivRules]
% 1.21/1.10  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.21/1.10  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.10  --sup_immed_bw_main                     []
% 1.21/1.10  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/1.10  --sup_input_triv                        [Unflattening;TrivRules]
% 1.21/1.10  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.10  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/1.10  
% 1.21/1.10  ------ Combination Options
% 1.21/1.10  
% 1.21/1.10  --comb_res_mult                         3
% 1.21/1.10  --comb_sup_mult                         2
% 1.21/1.10  --comb_inst_mult                        10
% 1.21/1.10  
% 1.21/1.10  ------ Debug Options
% 1.21/1.10  
% 1.21/1.10  --dbg_backtrace                         false
% 1.21/1.10  --dbg_dump_prop_clauses                 false
% 1.21/1.10  --dbg_dump_prop_clauses_file            -
% 1.21/1.10  --dbg_out_stat                          false
% 1.21/1.10  ------ Parsing...
% 1.21/1.10  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.21/1.10  
% 1.21/1.10  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.21/1.10  
% 1.21/1.10  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.21/1.10  
% 1.21/1.10  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.21/1.10  ------ Proving...
% 1.21/1.10  ------ Problem Properties 
% 1.21/1.10  
% 1.21/1.10  
% 1.21/1.10  clauses                                 20
% 1.21/1.10  conjectures                             4
% 1.21/1.10  EPR                                     7
% 1.21/1.10  Horn                                    15
% 1.21/1.10  unary                                   5
% 1.21/1.10  binary                                  11
% 1.21/1.10  lits                                    39
% 1.21/1.10  lits eq                                 7
% 1.21/1.10  fd_pure                                 0
% 1.21/1.10  fd_pseudo                               0
% 1.21/1.10  fd_cond                                 4
% 1.21/1.10  fd_pseudo_cond                          0
% 1.21/1.10  AC symbols                              0
% 1.21/1.10  
% 1.21/1.10  ------ Schedule dynamic 5 is on 
% 1.21/1.10  
% 1.21/1.10  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.21/1.10  
% 1.21/1.10  
% 1.21/1.10  ------ 
% 1.21/1.10  Current options:
% 1.21/1.10  ------ 
% 1.21/1.10  
% 1.21/1.10  ------ Input Options
% 1.21/1.10  
% 1.21/1.10  --out_options                           all
% 1.21/1.10  --tptp_safe_out                         true
% 1.21/1.10  --problem_path                          ""
% 1.21/1.10  --include_path                          ""
% 1.21/1.10  --clausifier                            res/vclausify_rel
% 1.21/1.10  --clausifier_options                    --mode clausify
% 1.21/1.10  --stdin                                 false
% 1.21/1.10  --stats_out                             all
% 1.21/1.10  
% 1.21/1.10  ------ General Options
% 1.21/1.10  
% 1.21/1.10  --fof                                   false
% 1.21/1.10  --time_out_real                         305.
% 1.21/1.10  --time_out_virtual                      -1.
% 1.21/1.10  --symbol_type_check                     false
% 1.21/1.10  --clausify_out                          false
% 1.21/1.10  --sig_cnt_out                           false
% 1.21/1.10  --trig_cnt_out                          false
% 1.21/1.10  --trig_cnt_out_tolerance                1.
% 1.21/1.10  --trig_cnt_out_sk_spl                   false
% 1.21/1.10  --abstr_cl_out                          false
% 1.21/1.10  
% 1.21/1.10  ------ Global Options
% 1.21/1.10  
% 1.21/1.10  --schedule                              default
% 1.21/1.10  --add_important_lit                     false
% 1.21/1.10  --prop_solver_per_cl                    1000
% 1.21/1.10  --min_unsat_core                        false
% 1.21/1.10  --soft_assumptions                      false
% 1.21/1.10  --soft_lemma_size                       3
% 1.21/1.10  --prop_impl_unit_size                   0
% 1.21/1.10  --prop_impl_unit                        []
% 1.21/1.10  --share_sel_clauses                     true
% 1.21/1.10  --reset_solvers                         false
% 1.21/1.10  --bc_imp_inh                            [conj_cone]
% 1.21/1.10  --conj_cone_tolerance                   3.
% 1.21/1.10  --extra_neg_conj                        none
% 1.21/1.10  --large_theory_mode                     true
% 1.21/1.10  --prolific_symb_bound                   200
% 1.21/1.10  --lt_threshold                          2000
% 1.21/1.10  --clause_weak_htbl                      true
% 1.21/1.10  --gc_record_bc_elim                     false
% 1.21/1.10  
% 1.21/1.10  ------ Preprocessing Options
% 1.21/1.10  
% 1.21/1.10  --preprocessing_flag                    true
% 1.21/1.10  --time_out_prep_mult                    0.1
% 1.21/1.10  --splitting_mode                        input
% 1.21/1.10  --splitting_grd                         true
% 1.21/1.10  --splitting_cvd                         false
% 1.21/1.10  --splitting_cvd_svl                     false
% 1.21/1.10  --splitting_nvd                         32
% 1.21/1.10  --sub_typing                            true
% 1.21/1.10  --prep_gs_sim                           true
% 1.21/1.10  --prep_unflatten                        true
% 1.21/1.10  --prep_res_sim                          true
% 1.21/1.10  --prep_upred                            true
% 1.21/1.10  --prep_sem_filter                       exhaustive
% 1.21/1.10  --prep_sem_filter_out                   false
% 1.21/1.10  --pred_elim                             true
% 1.21/1.10  --res_sim_input                         true
% 1.21/1.10  --eq_ax_congr_red                       true
% 1.21/1.10  --pure_diseq_elim                       true
% 1.21/1.10  --brand_transform                       false
% 1.21/1.10  --non_eq_to_eq                          false
% 1.21/1.10  --prep_def_merge                        true
% 1.21/1.10  --prep_def_merge_prop_impl              false
% 1.21/1.10  --prep_def_merge_mbd                    true
% 1.21/1.10  --prep_def_merge_tr_red                 false
% 1.21/1.10  --prep_def_merge_tr_cl                  false
% 1.21/1.10  --smt_preprocessing                     true
% 1.21/1.10  --smt_ac_axioms                         fast
% 1.21/1.10  --preprocessed_out                      false
% 1.21/1.10  --preprocessed_stats                    false
% 1.21/1.10  
% 1.21/1.10  ------ Abstraction refinement Options
% 1.21/1.10  
% 1.21/1.10  --abstr_ref                             []
% 1.21/1.10  --abstr_ref_prep                        false
% 1.21/1.10  --abstr_ref_until_sat                   false
% 1.21/1.10  --abstr_ref_sig_restrict                funpre
% 1.21/1.10  --abstr_ref_af_restrict_to_split_sk     false
% 1.21/1.10  --abstr_ref_under                       []
% 1.21/1.10  
% 1.21/1.10  ------ SAT Options
% 1.21/1.10  
% 1.21/1.10  --sat_mode                              false
% 1.21/1.10  --sat_fm_restart_options                ""
% 1.21/1.10  --sat_gr_def                            false
% 1.21/1.10  --sat_epr_types                         true
% 1.21/1.10  --sat_non_cyclic_types                  false
% 1.21/1.10  --sat_finite_models                     false
% 1.21/1.10  --sat_fm_lemmas                         false
% 1.21/1.10  --sat_fm_prep                           false
% 1.21/1.10  --sat_fm_uc_incr                        true
% 1.21/1.10  --sat_out_model                         small
% 1.21/1.10  --sat_out_clauses                       false
% 1.21/1.10  
% 1.21/1.10  ------ QBF Options
% 1.21/1.10  
% 1.21/1.10  --qbf_mode                              false
% 1.21/1.10  --qbf_elim_univ                         false
% 1.21/1.10  --qbf_dom_inst                          none
% 1.21/1.10  --qbf_dom_pre_inst                      false
% 1.21/1.10  --qbf_sk_in                             false
% 1.21/1.10  --qbf_pred_elim                         true
% 1.21/1.10  --qbf_split                             512
% 1.21/1.10  
% 1.21/1.10  ------ BMC1 Options
% 1.21/1.10  
% 1.21/1.10  --bmc1_incremental                      false
% 1.21/1.10  --bmc1_axioms                           reachable_all
% 1.21/1.10  --bmc1_min_bound                        0
% 1.21/1.10  --bmc1_max_bound                        -1
% 1.21/1.10  --bmc1_max_bound_default                -1
% 1.21/1.10  --bmc1_symbol_reachability              true
% 1.21/1.10  --bmc1_property_lemmas                  false
% 1.21/1.10  --bmc1_k_induction                      false
% 1.21/1.10  --bmc1_non_equiv_states                 false
% 1.21/1.10  --bmc1_deadlock                         false
% 1.21/1.10  --bmc1_ucm                              false
% 1.21/1.10  --bmc1_add_unsat_core                   none
% 1.21/1.10  --bmc1_unsat_core_children              false
% 1.21/1.10  --bmc1_unsat_core_extrapolate_axioms    false
% 1.21/1.10  --bmc1_out_stat                         full
% 1.21/1.10  --bmc1_ground_init                      false
% 1.21/1.10  --bmc1_pre_inst_next_state              false
% 1.21/1.10  --bmc1_pre_inst_state                   false
% 1.21/1.10  --bmc1_pre_inst_reach_state             false
% 1.21/1.10  --bmc1_out_unsat_core                   false
% 1.21/1.10  --bmc1_aig_witness_out                  false
% 1.21/1.10  --bmc1_verbose                          false
% 1.21/1.10  --bmc1_dump_clauses_tptp                false
% 1.21/1.10  --bmc1_dump_unsat_core_tptp             false
% 1.21/1.10  --bmc1_dump_file                        -
% 1.21/1.10  --bmc1_ucm_expand_uc_limit              128
% 1.21/1.10  --bmc1_ucm_n_expand_iterations          6
% 1.21/1.10  --bmc1_ucm_extend_mode                  1
% 1.21/1.10  --bmc1_ucm_init_mode                    2
% 1.21/1.10  --bmc1_ucm_cone_mode                    none
% 1.21/1.10  --bmc1_ucm_reduced_relation_type        0
% 1.21/1.10  --bmc1_ucm_relax_model                  4
% 1.21/1.10  --bmc1_ucm_full_tr_after_sat            true
% 1.21/1.10  --bmc1_ucm_expand_neg_assumptions       false
% 1.21/1.10  --bmc1_ucm_layered_model                none
% 1.21/1.10  --bmc1_ucm_max_lemma_size               10
% 1.21/1.10  
% 1.21/1.10  ------ AIG Options
% 1.21/1.10  
% 1.21/1.10  --aig_mode                              false
% 1.21/1.10  
% 1.21/1.10  ------ Instantiation Options
% 1.21/1.10  
% 1.21/1.10  --instantiation_flag                    true
% 1.21/1.10  --inst_sos_flag                         false
% 1.21/1.10  --inst_sos_phase                        true
% 1.21/1.10  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.21/1.10  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.21/1.10  --inst_lit_sel_side                     none
% 1.21/1.10  --inst_solver_per_active                1400
% 1.21/1.10  --inst_solver_calls_frac                1.
% 1.21/1.10  --inst_passive_queue_type               priority_queues
% 1.21/1.10  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.21/1.10  --inst_passive_queues_freq              [25;2]
% 1.21/1.10  --inst_dismatching                      true
% 1.21/1.10  --inst_eager_unprocessed_to_passive     true
% 1.21/1.10  --inst_prop_sim_given                   true
% 1.21/1.10  --inst_prop_sim_new                     false
% 1.21/1.10  --inst_subs_new                         false
% 1.21/1.10  --inst_eq_res_simp                      false
% 1.21/1.10  --inst_subs_given                       false
% 1.21/1.10  --inst_orphan_elimination               true
% 1.21/1.10  --inst_learning_loop_flag               true
% 1.21/1.10  --inst_learning_start                   3000
% 1.21/1.10  --inst_learning_factor                  2
% 1.21/1.10  --inst_start_prop_sim_after_learn       3
% 1.21/1.10  --inst_sel_renew                        solver
% 1.21/1.10  --inst_lit_activity_flag                true
% 1.21/1.10  --inst_restr_to_given                   false
% 1.21/1.10  --inst_activity_threshold               500
% 1.21/1.10  --inst_out_proof                        true
% 1.21/1.10  
% 1.21/1.10  ------ Resolution Options
% 1.21/1.10  
% 1.21/1.10  --resolution_flag                       false
% 1.21/1.10  --res_lit_sel                           adaptive
% 1.21/1.10  --res_lit_sel_side                      none
% 1.21/1.10  --res_ordering                          kbo
% 1.21/1.10  --res_to_prop_solver                    active
% 1.21/1.10  --res_prop_simpl_new                    false
% 1.21/1.10  --res_prop_simpl_given                  true
% 1.21/1.10  --res_passive_queue_type                priority_queues
% 1.21/1.10  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.21/1.10  --res_passive_queues_freq               [15;5]
% 1.21/1.10  --res_forward_subs                      full
% 1.21/1.10  --res_backward_subs                     full
% 1.21/1.10  --res_forward_subs_resolution           true
% 1.21/1.10  --res_backward_subs_resolution          true
% 1.21/1.10  --res_orphan_elimination                true
% 1.21/1.10  --res_time_limit                        2.
% 1.21/1.10  --res_out_proof                         true
% 1.21/1.10  
% 1.21/1.10  ------ Superposition Options
% 1.21/1.10  
% 1.21/1.10  --superposition_flag                    true
% 1.21/1.10  --sup_passive_queue_type                priority_queues
% 1.21/1.10  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.21/1.10  --sup_passive_queues_freq               [8;1;4]
% 1.21/1.10  --demod_completeness_check              fast
% 1.21/1.10  --demod_use_ground                      true
% 1.21/1.10  --sup_to_prop_solver                    passive
% 1.21/1.10  --sup_prop_simpl_new                    true
% 1.21/1.10  --sup_prop_simpl_given                  true
% 1.21/1.10  --sup_fun_splitting                     false
% 1.21/1.10  --sup_smt_interval                      50000
% 1.21/1.10  
% 1.21/1.10  ------ Superposition Simplification Setup
% 1.21/1.10  
% 1.21/1.10  --sup_indices_passive                   []
% 1.21/1.10  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.10  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.10  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.10  --sup_full_triv                         [TrivRules;PropSubs]
% 1.21/1.10  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.10  --sup_full_bw                           [BwDemod]
% 1.21/1.10  --sup_immed_triv                        [TrivRules]
% 1.21/1.10  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.21/1.10  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.10  --sup_immed_bw_main                     []
% 1.21/1.10  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/1.10  --sup_input_triv                        [Unflattening;TrivRules]
% 1.21/1.10  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.10  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/1.10  
% 1.21/1.10  ------ Combination Options
% 1.21/1.10  
% 1.21/1.10  --comb_res_mult                         3
% 1.21/1.10  --comb_sup_mult                         2
% 1.21/1.10  --comb_inst_mult                        10
% 1.21/1.10  
% 1.21/1.10  ------ Debug Options
% 1.21/1.10  
% 1.21/1.10  --dbg_backtrace                         false
% 1.21/1.10  --dbg_dump_prop_clauses                 false
% 1.21/1.10  --dbg_dump_prop_clauses_file            -
% 1.21/1.10  --dbg_out_stat                          false
% 1.21/1.10  
% 1.21/1.10  
% 1.21/1.10  
% 1.21/1.10  
% 1.21/1.10  ------ Proving...
% 1.21/1.10  
% 1.21/1.10  
% 1.21/1.10  % SZS status Theorem for theBenchmark.p
% 1.21/1.10  
% 1.21/1.10  % SZS output start CNFRefutation for theBenchmark.p
% 1.21/1.10  
% 1.21/1.10  fof(f11,conjecture,(
% 1.21/1.10    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.21/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.10  
% 1.21/1.10  fof(f12,negated_conjecture,(
% 1.21/1.10    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.21/1.10    inference(negated_conjecture,[],[f11])).
% 1.21/1.10  
% 1.21/1.10  fof(f23,plain,(
% 1.21/1.10    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.21/1.10    inference(ennf_transformation,[],[f12])).
% 1.21/1.10  
% 1.21/1.10  fof(f24,plain,(
% 1.21/1.10    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.21/1.10    inference(flattening,[],[f23])).
% 1.21/1.10  
% 1.21/1.10  fof(f33,plain,(
% 1.21/1.10    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 1.21/1.11    introduced(choice_axiom,[])).
% 1.21/1.11  
% 1.21/1.11  fof(f32,plain,(
% 1.21/1.11    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK2,X2),k8_setfam_1(sK2,sK3)) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 1.21/1.11    introduced(choice_axiom,[])).
% 1.21/1.11  
% 1.21/1.11  fof(f34,plain,(
% 1.21/1.11    (~r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 1.21/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f33,f32])).
% 1.21/1.11  
% 1.21/1.11  fof(f51,plain,(
% 1.21/1.11    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 1.21/1.11    inference(cnf_transformation,[],[f34])).
% 1.21/1.11  
% 1.21/1.11  fof(f6,axiom,(
% 1.21/1.11    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.21/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.11  
% 1.21/1.11  fof(f18,plain,(
% 1.21/1.11    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.21/1.11    inference(ennf_transformation,[],[f6])).
% 1.21/1.11  
% 1.21/1.11  fof(f44,plain,(
% 1.21/1.11    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.21/1.11    inference(cnf_transformation,[],[f18])).
% 1.21/1.11  
% 1.21/1.11  fof(f8,axiom,(
% 1.21/1.11    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.21/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.11  
% 1.21/1.11  fof(f20,plain,(
% 1.21/1.11    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.21/1.11    inference(ennf_transformation,[],[f8])).
% 1.21/1.11  
% 1.21/1.11  fof(f47,plain,(
% 1.21/1.11    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.21/1.11    inference(cnf_transformation,[],[f20])).
% 1.21/1.11  
% 1.21/1.11  fof(f53,plain,(
% 1.21/1.11    r1_tarski(sK3,sK4)),
% 1.21/1.11    inference(cnf_transformation,[],[f34])).
% 1.21/1.11  
% 1.21/1.11  fof(f54,plain,(
% 1.21/1.11    ~r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))),
% 1.21/1.11    inference(cnf_transformation,[],[f34])).
% 1.21/1.11  
% 1.21/1.11  fof(f4,axiom,(
% 1.21/1.11    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.21/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.11  
% 1.21/1.11  fof(f16,plain,(
% 1.21/1.11    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.21/1.11    inference(ennf_transformation,[],[f4])).
% 1.21/1.11  
% 1.21/1.11  fof(f41,plain,(
% 1.21/1.11    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.21/1.11    inference(cnf_transformation,[],[f16])).
% 1.21/1.11  
% 1.21/1.11  fof(f55,plain,(
% 1.21/1.11    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.21/1.11    inference(equality_resolution,[],[f41])).
% 1.21/1.11  
% 1.21/1.11  fof(f42,plain,(
% 1.21/1.11    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.21/1.11    inference(cnf_transformation,[],[f16])).
% 1.21/1.11  
% 1.21/1.11  fof(f2,axiom,(
% 1.21/1.11    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.21/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.11  
% 1.21/1.11  fof(f14,plain,(
% 1.21/1.11    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.21/1.11    inference(ennf_transformation,[],[f2])).
% 1.21/1.11  
% 1.21/1.11  fof(f37,plain,(
% 1.21/1.11    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.21/1.11    inference(cnf_transformation,[],[f14])).
% 1.21/1.11  
% 1.21/1.11  fof(f5,axiom,(
% 1.21/1.11    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.21/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.11  
% 1.21/1.11  fof(f17,plain,(
% 1.21/1.11    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.21/1.11    inference(ennf_transformation,[],[f5])).
% 1.21/1.11  
% 1.21/1.11  fof(f43,plain,(
% 1.21/1.11    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.21/1.11    inference(cnf_transformation,[],[f17])).
% 1.21/1.11  
% 1.21/1.11  fof(f9,axiom,(
% 1.21/1.11    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.21/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.11  
% 1.21/1.11  fof(f31,plain,(
% 1.21/1.11    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.21/1.11    inference(nnf_transformation,[],[f9])).
% 1.21/1.11  
% 1.21/1.11  fof(f49,plain,(
% 1.21/1.11    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.21/1.11    inference(cnf_transformation,[],[f31])).
% 1.21/1.11  
% 1.21/1.11  fof(f10,axiom,(
% 1.21/1.11    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.21/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.11  
% 1.21/1.11  fof(f21,plain,(
% 1.21/1.11    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.21/1.11    inference(ennf_transformation,[],[f10])).
% 1.21/1.11  
% 1.21/1.11  fof(f22,plain,(
% 1.21/1.11    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.21/1.11    inference(flattening,[],[f21])).
% 1.21/1.11  
% 1.21/1.11  fof(f50,plain,(
% 1.21/1.11    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 1.21/1.11    inference(cnf_transformation,[],[f22])).
% 1.21/1.11  
% 1.21/1.11  fof(f52,plain,(
% 1.21/1.11    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 1.21/1.11    inference(cnf_transformation,[],[f34])).
% 1.21/1.11  
% 1.21/1.11  fof(f1,axiom,(
% 1.21/1.11    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.21/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.11  
% 1.21/1.11  fof(f25,plain,(
% 1.21/1.11    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.21/1.11    inference(nnf_transformation,[],[f1])).
% 1.21/1.11  
% 1.21/1.11  fof(f26,plain,(
% 1.21/1.11    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.21/1.11    inference(rectify,[],[f25])).
% 1.21/1.11  
% 1.21/1.11  fof(f27,plain,(
% 1.21/1.11    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.21/1.11    introduced(choice_axiom,[])).
% 1.21/1.11  
% 1.21/1.11  fof(f28,plain,(
% 1.21/1.11    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.21/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 1.21/1.11  
% 1.21/1.11  fof(f36,plain,(
% 1.21/1.11    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.21/1.11    inference(cnf_transformation,[],[f28])).
% 1.21/1.11  
% 1.21/1.11  fof(f3,axiom,(
% 1.21/1.11    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.21/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.11  
% 1.21/1.11  fof(f13,plain,(
% 1.21/1.11    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.21/1.11    inference(rectify,[],[f3])).
% 1.21/1.11  
% 1.21/1.11  fof(f15,plain,(
% 1.21/1.11    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.21/1.11    inference(ennf_transformation,[],[f13])).
% 1.21/1.11  
% 1.21/1.11  fof(f29,plain,(
% 1.21/1.11    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.21/1.11    introduced(choice_axiom,[])).
% 1.21/1.11  
% 1.21/1.11  fof(f30,plain,(
% 1.21/1.11    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.21/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f29])).
% 1.21/1.11  
% 1.21/1.11  fof(f40,plain,(
% 1.21/1.11    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.21/1.11    inference(cnf_transformation,[],[f30])).
% 1.21/1.11  
% 1.21/1.11  fof(f45,plain,(
% 1.21/1.11    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.21/1.11    inference(cnf_transformation,[],[f18])).
% 1.21/1.11  
% 1.21/1.11  fof(f56,plain,(
% 1.21/1.11    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.21/1.11    inference(equality_resolution,[],[f45])).
% 1.21/1.11  
% 1.21/1.11  fof(f48,plain,(
% 1.21/1.11    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.21/1.11    inference(cnf_transformation,[],[f31])).
% 1.21/1.11  
% 1.21/1.11  fof(f7,axiom,(
% 1.21/1.11    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.21/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.11  
% 1.21/1.11  fof(f19,plain,(
% 1.21/1.11    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.21/1.11    inference(ennf_transformation,[],[f7])).
% 1.21/1.11  
% 1.21/1.11  fof(f46,plain,(
% 1.21/1.11    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.21/1.11    inference(cnf_transformation,[],[f19])).
% 1.21/1.11  
% 1.21/1.11  cnf(c_19,negated_conjecture,
% 1.21/1.11      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 1.21/1.11      inference(cnf_transformation,[],[f51]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_791,plain,
% 1.21/1.11      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 1.21/1.11      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_10,plain,
% 1.21/1.11      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.21/1.11      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 1.21/1.11      | k1_xboole_0 = X0 ),
% 1.21/1.11      inference(cnf_transformation,[],[f44]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_800,plain,
% 1.21/1.11      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 1.21/1.11      | k1_xboole_0 = X1
% 1.21/1.11      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.21/1.11      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2064,plain,
% 1.21/1.11      ( k6_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3) | sK3 = k1_xboole_0 ),
% 1.21/1.11      inference(superposition,[status(thm)],[c_791,c_800]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_12,plain,
% 1.21/1.11      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.21/1.11      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 1.21/1.11      inference(cnf_transformation,[],[f47]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_798,plain,
% 1.21/1.11      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 1.21/1.11      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.21/1.11      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1715,plain,
% 1.21/1.11      ( k6_setfam_1(sK2,sK3) = k1_setfam_1(sK3) ),
% 1.21/1.11      inference(superposition,[status(thm)],[c_791,c_798]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2067,plain,
% 1.21/1.11      ( k8_setfam_1(sK2,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 1.21/1.11      inference(light_normalisation,[status(thm)],[c_2064,c_1715]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_17,negated_conjecture,
% 1.21/1.11      ( r1_tarski(sK3,sK4) ),
% 1.21/1.11      inference(cnf_transformation,[],[f53]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_16,negated_conjecture,
% 1.21/1.11      ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
% 1.21/1.11      inference(cnf_transformation,[],[f54]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_7,plain,
% 1.21/1.11      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.21/1.11      inference(cnf_transformation,[],[f55]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_6,plain,
% 1.21/1.11      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 1.21/1.11      inference(cnf_transformation,[],[f42]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_48,plain,
% 1.21/1.11      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.21/1.11      | k1_xboole_0 = k1_xboole_0 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_6]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_322,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1040,plain,
% 1.21/1.11      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_322]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1041,plain,
% 1.21/1.11      ( sK4 != k1_xboole_0
% 1.21/1.11      | k1_xboole_0 = sK4
% 1.21/1.11      | k1_xboole_0 != k1_xboole_0 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_1040]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2,plain,
% 1.21/1.11      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.21/1.11      inference(cnf_transformation,[],[f37]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1044,plain,
% 1.21/1.11      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_2]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_321,plain,( X0 = X0 ),theory(equality) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1062,plain,
% 1.21/1.11      ( sK3 = sK3 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_321]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_8,plain,
% 1.21/1.11      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.21/1.11      | ~ v1_xboole_0(X1)
% 1.21/1.11      | v1_xboole_0(X0) ),
% 1.21/1.11      inference(cnf_transformation,[],[f43]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_13,plain,
% 1.21/1.11      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.21/1.11      inference(cnf_transformation,[],[f49]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_157,plain,
% 1.21/1.11      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.21/1.11      inference(prop_impl,[status(thm)],[c_13]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_188,plain,
% 1.21/1.11      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 1.21/1.11      inference(bin_hyper_res,[status(thm)],[c_8,c_157]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1150,plain,
% 1.21/1.11      ( ~ r1_tarski(sK3,X0) | ~ v1_xboole_0(X0) | v1_xboole_0(sK3) ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_188]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1152,plain,
% 1.21/1.11      ( ~ r1_tarski(sK3,k1_xboole_0)
% 1.21/1.11      | v1_xboole_0(sK3)
% 1.21/1.11      | ~ v1_xboole_0(k1_xboole_0) ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_1150]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_328,plain,
% 1.21/1.11      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.21/1.11      theory(equality) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_967,plain,
% 1.21/1.11      ( r1_tarski(X0,X1) | ~ r1_tarski(sK3,sK4) | X0 != sK3 | X1 != sK4 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_328]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1157,plain,
% 1.21/1.11      ( r1_tarski(sK3,X0)
% 1.21/1.11      | ~ r1_tarski(sK3,sK4)
% 1.21/1.11      | X0 != sK4
% 1.21/1.11      | sK3 != sK3 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_967]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1160,plain,
% 1.21/1.11      ( ~ r1_tarski(sK3,sK4)
% 1.21/1.11      | r1_tarski(sK3,k1_xboole_0)
% 1.21/1.11      | sK3 != sK3
% 1.21/1.11      | k1_xboole_0 != sK4 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_1157]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_15,plain,
% 1.21/1.11      ( ~ r1_tarski(X0,X1)
% 1.21/1.11      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 1.21/1.11      | k1_xboole_0 = X0 ),
% 1.21/1.11      inference(cnf_transformation,[],[f50]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1046,plain,
% 1.21/1.11      ( r1_tarski(k1_setfam_1(X0),k1_setfam_1(sK3))
% 1.21/1.11      | ~ r1_tarski(sK3,X0)
% 1.21/1.11      | k1_xboole_0 = sK3 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_15]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1213,plain,
% 1.21/1.11      ( r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3))
% 1.21/1.11      | ~ r1_tarski(sK3,sK4)
% 1.21/1.11      | k1_xboole_0 = sK3 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_1046]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1339,plain,
% 1.21/1.11      ( r1_tarski(X0,X1)
% 1.21/1.11      | ~ r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3))
% 1.21/1.11      | X1 != k1_setfam_1(sK3)
% 1.21/1.11      | X0 != k1_setfam_1(sK4) ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_328]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1550,plain,
% 1.21/1.11      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
% 1.21/1.11      | ~ r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3))
% 1.21/1.11      | k8_setfam_1(sK2,sK3) != k1_setfam_1(sK3)
% 1.21/1.11      | k8_setfam_1(sK2,sK4) != k1_setfam_1(sK4) ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_1339]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1232,plain,
% 1.21/1.11      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_322]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1934,plain,
% 1.21/1.11      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_1232]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1935,plain,
% 1.21/1.11      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_1934]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_18,negated_conjecture,
% 1.21/1.11      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 1.21/1.11      inference(cnf_transformation,[],[f52]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_792,plain,
% 1.21/1.11      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 1.21/1.11      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2063,plain,
% 1.21/1.11      ( k6_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4) | sK4 = k1_xboole_0 ),
% 1.21/1.11      inference(superposition,[status(thm)],[c_792,c_800]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1714,plain,
% 1.21/1.11      ( k6_setfam_1(sK2,sK4) = k1_setfam_1(sK4) ),
% 1.21/1.11      inference(superposition,[status(thm)],[c_792,c_798]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2072,plain,
% 1.21/1.11      ( k8_setfam_1(sK2,sK4) = k1_setfam_1(sK4) | sK4 = k1_xboole_0 ),
% 1.21/1.11      inference(light_normalisation,[status(thm)],[c_2063,c_1714]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_0,plain,
% 1.21/1.11      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.21/1.11      inference(cnf_transformation,[],[f36]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_809,plain,
% 1.21/1.11      ( r2_hidden(sK0(X0),X0) = iProver_top
% 1.21/1.11      | v1_xboole_0(X0) = iProver_top ),
% 1.21/1.11      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_802,plain,
% 1.21/1.11      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.21/1.11      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_3,plain,
% 1.21/1.11      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 1.21/1.11      inference(cnf_transformation,[],[f40]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_806,plain,
% 1.21/1.11      ( r1_xboole_0(X0,X1) != iProver_top
% 1.21/1.11      | r2_hidden(X2,X0) != iProver_top
% 1.21/1.11      | r2_hidden(X2,X1) != iProver_top ),
% 1.21/1.11      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2277,plain,
% 1.21/1.11      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.21/1.11      inference(superposition,[status(thm)],[c_802,c_806]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2286,plain,
% 1.21/1.11      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.21/1.11      inference(superposition,[status(thm)],[c_809,c_2277]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2295,plain,
% 1.21/1.11      ( v1_xboole_0(k1_xboole_0) ),
% 1.21/1.11      inference(predicate_to_equality_rev,[status(thm)],[c_2286]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2459,plain,
% 1.21/1.11      ( sK3 = k1_xboole_0 ),
% 1.21/1.11      inference(global_propositional_subsumption,
% 1.21/1.11                [status(thm)],
% 1.21/1.11                [c_2067,c_17,c_16,c_7,c_48,c_1041,c_1044,c_1062,c_1152,
% 1.21/1.11                 c_1160,c_1213,c_1550,c_1935,c_2072,c_2295]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2469,plain,
% 1.21/1.11      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 1.21/1.11      inference(demodulation,[status(thm)],[c_2459,c_791]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_9,plain,
% 1.21/1.11      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 1.21/1.11      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 1.21/1.11      inference(cnf_transformation,[],[f56]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_801,plain,
% 1.21/1.11      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 1.21/1.11      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.21/1.11      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2559,plain,
% 1.21/1.11      ( k8_setfam_1(sK2,k1_xboole_0) = sK2 ),
% 1.21/1.11      inference(superposition,[status(thm)],[c_2469,c_801]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_794,plain,
% 1.21/1.11      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
% 1.21/1.11      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2468,plain,
% 1.21/1.11      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
% 1.21/1.11      inference(demodulation,[status(thm)],[c_2459,c_794]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_2637,plain,
% 1.21/1.11      ( r1_tarski(k8_setfam_1(sK2,sK4),sK2) != iProver_top ),
% 1.21/1.11      inference(demodulation,[status(thm)],[c_2559,c_2468]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_14,plain,
% 1.21/1.11      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.21/1.11      inference(cnf_transformation,[],[f48]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_999,plain,
% 1.21/1.11      ( r1_tarski(k8_setfam_1(sK2,sK4),sK2)
% 1.21/1.11      | ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_14]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_1000,plain,
% 1.21/1.11      ( r1_tarski(k8_setfam_1(sK2,sK4),sK2) = iProver_top
% 1.21/1.11      | m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top ),
% 1.21/1.11      inference(predicate_to_equality,[status(thm)],[c_999]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_11,plain,
% 1.21/1.11      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.21/1.11      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 1.21/1.11      inference(cnf_transformation,[],[f46]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_941,plain,
% 1.21/1.11      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
% 1.21/1.11      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 1.21/1.11      inference(instantiation,[status(thm)],[c_11]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_942,plain,
% 1.21/1.11      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) = iProver_top
% 1.21/1.11      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
% 1.21/1.11      inference(predicate_to_equality,[status(thm)],[c_941]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(c_21,plain,
% 1.21/1.11      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 1.21/1.11      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.21/1.11  
% 1.21/1.11  cnf(contradiction,plain,
% 1.21/1.11      ( $false ),
% 1.21/1.11      inference(minisat,[status(thm)],[c_2637,c_1000,c_942,c_21]) ).
% 1.21/1.11  
% 1.21/1.11  
% 1.21/1.11  % SZS output end CNFRefutation for theBenchmark.p
% 1.21/1.11  
% 1.21/1.11  ------                               Statistics
% 1.21/1.11  
% 1.21/1.11  ------ General
% 1.21/1.11  
% 1.21/1.11  abstr_ref_over_cycles:                  0
% 1.21/1.11  abstr_ref_under_cycles:                 0
% 1.21/1.11  gc_basic_clause_elim:                   0
% 1.21/1.11  forced_gc_time:                         0
% 1.21/1.11  parsing_time:                           0.009
% 1.21/1.11  unif_index_cands_time:                  0.
% 1.21/1.11  unif_index_add_time:                    0.
% 1.21/1.11  orderings_time:                         0.
% 1.21/1.11  out_proof_time:                         0.021
% 1.21/1.11  total_time:                             0.125
% 1.21/1.11  num_of_symbols:                         46
% 1.21/1.11  num_of_terms:                           1576
% 1.21/1.11  
% 1.21/1.11  ------ Preprocessing
% 1.21/1.11  
% 1.21/1.11  num_of_splits:                          0
% 1.21/1.11  num_of_split_atoms:                     0
% 1.21/1.11  num_of_reused_defs:                     0
% 1.21/1.11  num_eq_ax_congr_red:                    16
% 1.21/1.11  num_of_sem_filtered_clauses:            1
% 1.21/1.11  num_of_subtypes:                        0
% 1.21/1.11  monotx_restored_types:                  0
% 1.21/1.11  sat_num_of_epr_types:                   0
% 1.21/1.11  sat_num_of_non_cyclic_types:            0
% 1.21/1.11  sat_guarded_non_collapsed_types:        0
% 1.21/1.11  num_pure_diseq_elim:                    0
% 1.21/1.11  simp_replaced_by:                       0
% 1.21/1.11  res_preprocessed:                       77
% 1.21/1.11  prep_upred:                             0
% 1.21/1.11  prep_unflattend:                        7
% 1.21/1.11  smt_new_axioms:                         0
% 1.21/1.11  pred_elim_cands:                        5
% 1.21/1.11  pred_elim:                              0
% 1.21/1.11  pred_elim_cl:                           0
% 1.21/1.11  pred_elim_cycles:                       1
% 1.21/1.11  merged_defs:                            6
% 1.21/1.11  merged_defs_ncl:                        0
% 1.21/1.11  bin_hyper_res:                          7
% 1.21/1.11  prep_cycles:                            3
% 1.21/1.11  pred_elim_time:                         0.001
% 1.21/1.11  splitting_time:                         0.
% 1.21/1.11  sem_filter_time:                        0.
% 1.21/1.11  monotx_time:                            0.001
% 1.21/1.11  subtype_inf_time:                       0.
% 1.21/1.11  
% 1.21/1.11  ------ Problem properties
% 1.21/1.11  
% 1.21/1.11  clauses:                                20
% 1.21/1.11  conjectures:                            4
% 1.21/1.11  epr:                                    7
% 1.21/1.11  horn:                                   15
% 1.21/1.11  ground:                                 5
% 1.21/1.11  unary:                                  5
% 1.21/1.11  binary:                                 11
% 1.21/1.11  lits:                                   39
% 1.21/1.11  lits_eq:                                7
% 1.21/1.11  fd_pure:                                0
% 1.21/1.11  fd_pseudo:                              0
% 1.21/1.11  fd_cond:                                4
% 1.21/1.11  fd_pseudo_cond:                         0
% 1.21/1.11  ac_symbols:                             0
% 1.21/1.11  
% 1.21/1.11  ------ Propositional Solver
% 1.21/1.11  
% 1.21/1.11  prop_solver_calls:                      24
% 1.21/1.11  prop_fast_solver_calls:                 416
% 1.21/1.11  smt_solver_calls:                       0
% 1.21/1.11  smt_fast_solver_calls:                  0
% 1.21/1.11  prop_num_of_clauses:                    923
% 1.21/1.11  prop_preprocess_simplified:             3370
% 1.21/1.11  prop_fo_subsumed:                       1
% 1.21/1.11  prop_solver_time:                       0.
% 1.21/1.11  smt_solver_time:                        0.
% 1.21/1.11  smt_fast_solver_time:                   0.
% 1.21/1.11  prop_fast_solver_time:                  0.
% 1.21/1.11  prop_unsat_core_time:                   0.
% 1.21/1.11  
% 1.21/1.11  ------ QBF
% 1.21/1.11  
% 1.21/1.11  qbf_q_res:                              0
% 1.21/1.11  qbf_num_tautologies:                    0
% 1.21/1.11  qbf_prep_cycles:                        0
% 1.21/1.11  
% 1.21/1.11  ------ BMC1
% 1.21/1.11  
% 1.21/1.11  bmc1_current_bound:                     -1
% 1.21/1.11  bmc1_last_solved_bound:                 -1
% 1.21/1.11  bmc1_unsat_core_size:                   -1
% 1.21/1.11  bmc1_unsat_core_parents_size:           -1
% 1.21/1.11  bmc1_merge_next_fun:                    0
% 1.21/1.11  bmc1_unsat_core_clauses_time:           0.
% 1.21/1.11  
% 1.21/1.11  ------ Instantiation
% 1.21/1.11  
% 1.21/1.11  inst_num_of_clauses:                    300
% 1.21/1.11  inst_num_in_passive:                    74
% 1.21/1.11  inst_num_in_active:                     180
% 1.21/1.11  inst_num_in_unprocessed:                47
% 1.21/1.11  inst_num_of_loops:                      220
% 1.21/1.11  inst_num_of_learning_restarts:          0
% 1.21/1.11  inst_num_moves_active_passive:          37
% 1.21/1.11  inst_lit_activity:                      0
% 1.21/1.11  inst_lit_activity_moves:                0
% 1.21/1.11  inst_num_tautologies:                   0
% 1.21/1.11  inst_num_prop_implied:                  0
% 1.21/1.11  inst_num_existing_simplified:           0
% 1.21/1.11  inst_num_eq_res_simplified:             0
% 1.21/1.11  inst_num_child_elim:                    0
% 1.21/1.11  inst_num_of_dismatching_blockings:      78
% 1.21/1.11  inst_num_of_non_proper_insts:           246
% 1.21/1.11  inst_num_of_duplicates:                 0
% 1.21/1.11  inst_inst_num_from_inst_to_res:         0
% 1.21/1.11  inst_dismatching_checking_time:         0.
% 1.21/1.11  
% 1.21/1.11  ------ Resolution
% 1.21/1.11  
% 1.21/1.11  res_num_of_clauses:                     0
% 1.21/1.11  res_num_in_passive:                     0
% 1.21/1.11  res_num_in_active:                      0
% 1.21/1.11  res_num_of_loops:                       80
% 1.21/1.11  res_forward_subset_subsumed:            16
% 1.21/1.11  res_backward_subset_subsumed:           2
% 1.21/1.11  res_forward_subsumed:                   0
% 1.21/1.11  res_backward_subsumed:                  0
% 1.21/1.11  res_forward_subsumption_resolution:     0
% 1.21/1.11  res_backward_subsumption_resolution:    0
% 1.21/1.11  res_clause_to_clause_subsumption:       84
% 1.21/1.11  res_orphan_elimination:                 0
% 1.21/1.11  res_tautology_del:                      36
% 1.21/1.11  res_num_eq_res_simplified:              0
% 1.21/1.11  res_num_sel_changes:                    0
% 1.21/1.11  res_moves_from_active_to_pass:          0
% 1.21/1.11  
% 1.21/1.11  ------ Superposition
% 1.21/1.11  
% 1.21/1.11  sup_time_total:                         0.
% 1.21/1.11  sup_time_generating:                    0.
% 1.21/1.11  sup_time_sim_full:                      0.
% 1.21/1.11  sup_time_sim_immed:                     0.
% 1.21/1.11  
% 1.21/1.11  sup_num_of_clauses:                     52
% 1.21/1.11  sup_num_in_active:                      33
% 1.21/1.11  sup_num_in_passive:                     19
% 1.21/1.11  sup_num_of_loops:                       43
% 1.21/1.11  sup_fw_superposition:                   25
% 1.21/1.11  sup_bw_superposition:                   23
% 1.21/1.11  sup_immediate_simplified:               6
% 1.21/1.11  sup_given_eliminated:                   0
% 1.21/1.11  comparisons_done:                       0
% 1.21/1.11  comparisons_avoided:                    2
% 1.21/1.11  
% 1.21/1.11  ------ Simplifications
% 1.21/1.11  
% 1.21/1.11  
% 1.21/1.11  sim_fw_subset_subsumed:                 3
% 1.21/1.11  sim_bw_subset_subsumed:                 0
% 1.21/1.11  sim_fw_subsumed:                        1
% 1.21/1.11  sim_bw_subsumed:                        0
% 1.21/1.11  sim_fw_subsumption_res:                 0
% 1.21/1.11  sim_bw_subsumption_res:                 0
% 1.21/1.11  sim_tautology_del:                      2
% 1.21/1.11  sim_eq_tautology_del:                   2
% 1.21/1.11  sim_eq_res_simp:                        0
% 1.21/1.11  sim_fw_demodulated:                     0
% 1.21/1.11  sim_bw_demodulated:                     10
% 1.21/1.11  sim_light_normalised:                   2
% 1.21/1.11  sim_joinable_taut:                      0
% 1.21/1.11  sim_joinable_simp:                      0
% 1.21/1.11  sim_ac_normalised:                      0
% 1.21/1.11  sim_smt_subsumption:                    0
% 1.21/1.11  
%------------------------------------------------------------------------------
