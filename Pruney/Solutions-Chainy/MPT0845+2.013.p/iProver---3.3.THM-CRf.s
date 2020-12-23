%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:17 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 212 expanded)
%              Number of clauses        :   69 (  78 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  328 ( 595 expanded)
%              Number of equality atoms :  116 ( 146 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f40])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f50,f71])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f30,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK4)
          | ~ r2_hidden(X1,sK4) )
      & k1_xboole_0 != sK4 ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK4)
        | ~ r2_hidden(X1,sK4) )
    & k1_xboole_0 != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f42])).

fof(f69,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK4)
      | ~ r2_hidden(X1,sK4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK2(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,plain,
    ( m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_813,plain,
    ( m1_subset_1(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_812,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_814,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1857,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_812,c_814])).

cnf(c_5,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1859,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1857,c_5,c_7])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k3_subset_1(X1,X2))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_811,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2292,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1859,c_811])).

cnf(c_34,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6084,plain,
    ( m1_subset_1(X1,X0) != iProver_top
    | k1_xboole_0 = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2292,c_34])).

cnf(c_6085,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6084])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_235,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_236,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_807,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_6092,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6085,c_807])).

cnf(c_6095,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_6092])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_820,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X1),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_818,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK2(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1285,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_820,c_818])).

cnf(c_20,negated_conjecture,
    ( ~ r1_xboole_0(X0,sK4)
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_809,plain,
    ( r1_xboole_0(X0,sK4) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3200,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_809])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_124,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_1])).

cnf(c_125,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_124])).

cnf(c_991,plain,
    ( m1_subset_1(X0,sK4)
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_992,plain,
    ( m1_subset_1(X0,sK4) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_991])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1017,plain,
    ( r2_hidden(sK0(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1018,plain,
    ( r2_hidden(sK0(sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1017])).

cnf(c_1076,plain,
    ( r2_hidden(sK2(sK4),sK4)
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1080,plain,
    ( r2_hidden(sK2(sK4),sK4) = iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1076])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1249,plain,
    ( ~ m1_subset_1(X0,sK4)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1250,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_823,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1286,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_820,c_823])).

cnf(c_1537,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_809])).

cnf(c_1666,plain,
    ( ~ r1_xboole_0(sK2(sK4),sK4)
    | ~ r2_hidden(sK2(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1667,plain,
    ( r1_xboole_0(sK2(sK4),sK4) != iProver_top
    | r2_hidden(sK2(sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1666])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_958,plain,
    ( r1_xboole_0(X0,sK4)
    | r2_hidden(sK1(X0,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2117,plain,
    ( r1_xboole_0(sK2(sK4),sK4)
    | r2_hidden(sK1(sK2(sK4),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_2118,plain,
    ( r1_xboole_0(sK2(sK4),sK4) = iProver_top
    | r2_hidden(sK1(sK2(sK4),sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2117])).

cnf(c_963,plain,
    ( r1_xboole_0(X0,sK4)
    | r2_hidden(sK1(X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2116,plain,
    ( r1_xboole_0(sK2(sK4),sK4)
    | r2_hidden(sK1(sK2(sK4),sK4),sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_2120,plain,
    ( r1_xboole_0(sK2(sK4),sK4) = iProver_top
    | r2_hidden(sK1(sK2(sK4),sK4),sK2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2116])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X0,sK2(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2622,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(sK1(sK2(sK4),sK4),sK2(sK4))
    | ~ r2_hidden(sK1(sK2(sK4),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2629,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK1(sK2(sK4),sK4),sK2(sK4)) != iProver_top
    | r2_hidden(sK1(sK2(sK4),sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2622])).

cnf(c_3775,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3200,c_992,c_1018,c_1080,c_1250,c_1537,c_1667,c_2118,c_2120,c_2629])).

cnf(c_6167,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6095,c_3775])).

cnf(c_485,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_968,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_969,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_484,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_499,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6167,c_969,c_499,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.00/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.00  
% 3.00/1.00  ------  iProver source info
% 3.00/1.00  
% 3.00/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.00  git: non_committed_changes: false
% 3.00/1.00  git: last_make_outside_of_git: false
% 3.00/1.00  
% 3.00/1.00  ------ 
% 3.00/1.00  
% 3.00/1.00  ------ Input Options
% 3.00/1.00  
% 3.00/1.00  --out_options                           all
% 3.00/1.00  --tptp_safe_out                         true
% 3.00/1.00  --problem_path                          ""
% 3.00/1.00  --include_path                          ""
% 3.00/1.00  --clausifier                            res/vclausify_rel
% 3.00/1.00  --clausifier_options                    --mode clausify
% 3.00/1.00  --stdin                                 false
% 3.00/1.00  --stats_out                             all
% 3.00/1.00  
% 3.00/1.00  ------ General Options
% 3.00/1.00  
% 3.00/1.00  --fof                                   false
% 3.00/1.00  --time_out_real                         305.
% 3.00/1.00  --time_out_virtual                      -1.
% 3.00/1.00  --symbol_type_check                     false
% 3.00/1.00  --clausify_out                          false
% 3.00/1.00  --sig_cnt_out                           false
% 3.00/1.00  --trig_cnt_out                          false
% 3.00/1.00  --trig_cnt_out_tolerance                1.
% 3.00/1.00  --trig_cnt_out_sk_spl                   false
% 3.00/1.00  --abstr_cl_out                          false
% 3.00/1.00  
% 3.00/1.00  ------ Global Options
% 3.00/1.00  
% 3.00/1.00  --schedule                              default
% 3.00/1.00  --add_important_lit                     false
% 3.00/1.00  --prop_solver_per_cl                    1000
% 3.00/1.00  --min_unsat_core                        false
% 3.00/1.00  --soft_assumptions                      false
% 3.00/1.00  --soft_lemma_size                       3
% 3.00/1.00  --prop_impl_unit_size                   0
% 3.00/1.00  --prop_impl_unit                        []
% 3.00/1.00  --share_sel_clauses                     true
% 3.00/1.00  --reset_solvers                         false
% 3.00/1.00  --bc_imp_inh                            [conj_cone]
% 3.00/1.00  --conj_cone_tolerance                   3.
% 3.00/1.00  --extra_neg_conj                        none
% 3.00/1.00  --large_theory_mode                     true
% 3.00/1.00  --prolific_symb_bound                   200
% 3.00/1.00  --lt_threshold                          2000
% 3.00/1.00  --clause_weak_htbl                      true
% 3.00/1.00  --gc_record_bc_elim                     false
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing Options
% 3.00/1.00  
% 3.00/1.00  --preprocessing_flag                    true
% 3.00/1.00  --time_out_prep_mult                    0.1
% 3.00/1.00  --splitting_mode                        input
% 3.00/1.00  --splitting_grd                         true
% 3.00/1.00  --splitting_cvd                         false
% 3.00/1.00  --splitting_cvd_svl                     false
% 3.00/1.00  --splitting_nvd                         32
% 3.00/1.00  --sub_typing                            true
% 3.00/1.00  --prep_gs_sim                           true
% 3.00/1.00  --prep_unflatten                        true
% 3.00/1.00  --prep_res_sim                          true
% 3.00/1.00  --prep_upred                            true
% 3.00/1.00  --prep_sem_filter                       exhaustive
% 3.00/1.00  --prep_sem_filter_out                   false
% 3.00/1.00  --pred_elim                             true
% 3.00/1.00  --res_sim_input                         true
% 3.00/1.00  --eq_ax_congr_red                       true
% 3.00/1.00  --pure_diseq_elim                       true
% 3.00/1.00  --brand_transform                       false
% 3.00/1.00  --non_eq_to_eq                          false
% 3.00/1.00  --prep_def_merge                        true
% 3.00/1.00  --prep_def_merge_prop_impl              false
% 3.00/1.00  --prep_def_merge_mbd                    true
% 3.00/1.00  --prep_def_merge_tr_red                 false
% 3.00/1.00  --prep_def_merge_tr_cl                  false
% 3.00/1.00  --smt_preprocessing                     true
% 3.00/1.00  --smt_ac_axioms                         fast
% 3.00/1.00  --preprocessed_out                      false
% 3.00/1.00  --preprocessed_stats                    false
% 3.00/1.00  
% 3.00/1.00  ------ Abstraction refinement Options
% 3.00/1.00  
% 3.00/1.00  --abstr_ref                             []
% 3.00/1.00  --abstr_ref_prep                        false
% 3.00/1.00  --abstr_ref_until_sat                   false
% 3.00/1.00  --abstr_ref_sig_restrict                funpre
% 3.00/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.00  --abstr_ref_under                       []
% 3.00/1.00  
% 3.00/1.00  ------ SAT Options
% 3.00/1.00  
% 3.00/1.00  --sat_mode                              false
% 3.00/1.00  --sat_fm_restart_options                ""
% 3.00/1.00  --sat_gr_def                            false
% 3.00/1.00  --sat_epr_types                         true
% 3.00/1.00  --sat_non_cyclic_types                  false
% 3.00/1.00  --sat_finite_models                     false
% 3.00/1.00  --sat_fm_lemmas                         false
% 3.00/1.00  --sat_fm_prep                           false
% 3.00/1.00  --sat_fm_uc_incr                        true
% 3.00/1.00  --sat_out_model                         small
% 3.00/1.00  --sat_out_clauses                       false
% 3.00/1.00  
% 3.00/1.00  ------ QBF Options
% 3.00/1.00  
% 3.00/1.00  --qbf_mode                              false
% 3.00/1.00  --qbf_elim_univ                         false
% 3.00/1.00  --qbf_dom_inst                          none
% 3.00/1.00  --qbf_dom_pre_inst                      false
% 3.00/1.00  --qbf_sk_in                             false
% 3.00/1.00  --qbf_pred_elim                         true
% 3.00/1.00  --qbf_split                             512
% 3.00/1.00  
% 3.00/1.00  ------ BMC1 Options
% 3.00/1.00  
% 3.00/1.00  --bmc1_incremental                      false
% 3.00/1.00  --bmc1_axioms                           reachable_all
% 3.00/1.00  --bmc1_min_bound                        0
% 3.00/1.00  --bmc1_max_bound                        -1
% 3.00/1.00  --bmc1_max_bound_default                -1
% 3.00/1.00  --bmc1_symbol_reachability              true
% 3.00/1.00  --bmc1_property_lemmas                  false
% 3.00/1.00  --bmc1_k_induction                      false
% 3.00/1.00  --bmc1_non_equiv_states                 false
% 3.00/1.00  --bmc1_deadlock                         false
% 3.00/1.00  --bmc1_ucm                              false
% 3.00/1.00  --bmc1_add_unsat_core                   none
% 3.00/1.00  --bmc1_unsat_core_children              false
% 3.00/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.00  --bmc1_out_stat                         full
% 3.00/1.00  --bmc1_ground_init                      false
% 3.00/1.00  --bmc1_pre_inst_next_state              false
% 3.00/1.00  --bmc1_pre_inst_state                   false
% 3.00/1.00  --bmc1_pre_inst_reach_state             false
% 3.00/1.00  --bmc1_out_unsat_core                   false
% 3.00/1.00  --bmc1_aig_witness_out                  false
% 3.00/1.00  --bmc1_verbose                          false
% 3.00/1.00  --bmc1_dump_clauses_tptp                false
% 3.00/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.00  --bmc1_dump_file                        -
% 3.00/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.00  --bmc1_ucm_extend_mode                  1
% 3.00/1.00  --bmc1_ucm_init_mode                    2
% 3.00/1.00  --bmc1_ucm_cone_mode                    none
% 3.00/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.00  --bmc1_ucm_relax_model                  4
% 3.00/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.00  --bmc1_ucm_layered_model                none
% 3.00/1.00  --bmc1_ucm_max_lemma_size               10
% 3.00/1.00  
% 3.00/1.00  ------ AIG Options
% 3.00/1.00  
% 3.00/1.00  --aig_mode                              false
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation Options
% 3.00/1.00  
% 3.00/1.00  --instantiation_flag                    true
% 3.00/1.00  --inst_sos_flag                         false
% 3.00/1.00  --inst_sos_phase                        true
% 3.00/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel_side                     num_symb
% 3.00/1.00  --inst_solver_per_active                1400
% 3.00/1.00  --inst_solver_calls_frac                1.
% 3.00/1.00  --inst_passive_queue_type               priority_queues
% 3.00/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.00  --inst_passive_queues_freq              [25;2]
% 3.00/1.00  --inst_dismatching                      true
% 3.00/1.00  --inst_eager_unprocessed_to_passive     true
% 3.00/1.00  --inst_prop_sim_given                   true
% 3.00/1.00  --inst_prop_sim_new                     false
% 3.00/1.00  --inst_subs_new                         false
% 3.00/1.00  --inst_eq_res_simp                      false
% 3.00/1.00  --inst_subs_given                       false
% 3.00/1.00  --inst_orphan_elimination               true
% 3.00/1.00  --inst_learning_loop_flag               true
% 3.00/1.00  --inst_learning_start                   3000
% 3.00/1.00  --inst_learning_factor                  2
% 3.00/1.00  --inst_start_prop_sim_after_learn       3
% 3.00/1.00  --inst_sel_renew                        solver
% 3.00/1.00  --inst_lit_activity_flag                true
% 3.00/1.00  --inst_restr_to_given                   false
% 3.00/1.00  --inst_activity_threshold               500
% 3.00/1.00  --inst_out_proof                        true
% 3.00/1.00  
% 3.00/1.00  ------ Resolution Options
% 3.00/1.00  
% 3.00/1.00  --resolution_flag                       true
% 3.00/1.00  --res_lit_sel                           adaptive
% 3.00/1.00  --res_lit_sel_side                      none
% 3.00/1.00  --res_ordering                          kbo
% 3.00/1.00  --res_to_prop_solver                    active
% 3.00/1.00  --res_prop_simpl_new                    false
% 3.00/1.00  --res_prop_simpl_given                  true
% 3.00/1.00  --res_passive_queue_type                priority_queues
% 3.00/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.00  --res_passive_queues_freq               [15;5]
% 3.00/1.00  --res_forward_subs                      full
% 3.00/1.00  --res_backward_subs                     full
% 3.00/1.00  --res_forward_subs_resolution           true
% 3.00/1.00  --res_backward_subs_resolution          true
% 3.00/1.00  --res_orphan_elimination                true
% 3.00/1.00  --res_time_limit                        2.
% 3.00/1.00  --res_out_proof                         true
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Options
% 3.00/1.00  
% 3.00/1.00  --superposition_flag                    true
% 3.00/1.00  --sup_passive_queue_type                priority_queues
% 3.00/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.00  --demod_completeness_check              fast
% 3.00/1.00  --demod_use_ground                      true
% 3.00/1.00  --sup_to_prop_solver                    passive
% 3.00/1.00  --sup_prop_simpl_new                    true
% 3.00/1.00  --sup_prop_simpl_given                  true
% 3.00/1.00  --sup_fun_splitting                     false
% 3.00/1.00  --sup_smt_interval                      50000
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Simplification Setup
% 3.00/1.00  
% 3.00/1.00  --sup_indices_passive                   []
% 3.00/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_full_bw                           [BwDemod]
% 3.00/1.00  --sup_immed_triv                        [TrivRules]
% 3.00/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_immed_bw_main                     []
% 3.00/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  
% 3.00/1.00  ------ Combination Options
% 3.00/1.00  
% 3.00/1.00  --comb_res_mult                         3
% 3.00/1.00  --comb_sup_mult                         2
% 3.00/1.00  --comb_inst_mult                        10
% 3.00/1.00  
% 3.00/1.00  ------ Debug Options
% 3.00/1.00  
% 3.00/1.00  --dbg_backtrace                         false
% 3.00/1.00  --dbg_dump_prop_clauses                 false
% 3.00/1.00  --dbg_dump_prop_clauses_file            -
% 3.00/1.00  --dbg_out_stat                          false
% 3.00/1.00  ------ Parsing...
% 3.00/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.00  ------ Proving...
% 3.00/1.00  ------ Problem Properties 
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  clauses                                 21
% 3.00/1.00  conjectures                             2
% 3.00/1.00  EPR                                     9
% 3.00/1.00  Horn                                    16
% 3.00/1.00  unary                                   6
% 3.00/1.00  binary                                  8
% 3.00/1.00  lits                                    45
% 3.00/1.00  lits eq                                 5
% 3.00/1.00  fd_pure                                 0
% 3.00/1.00  fd_pseudo                               0
% 3.00/1.00  fd_cond                                 1
% 3.00/1.00  fd_pseudo_cond                          0
% 3.00/1.00  AC symbols                              0
% 3.00/1.00  
% 3.00/1.00  ------ Schedule dynamic 5 is on 
% 3.00/1.00  
% 3.00/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  ------ 
% 3.00/1.00  Current options:
% 3.00/1.00  ------ 
% 3.00/1.00  
% 3.00/1.00  ------ Input Options
% 3.00/1.00  
% 3.00/1.00  --out_options                           all
% 3.00/1.00  --tptp_safe_out                         true
% 3.00/1.00  --problem_path                          ""
% 3.00/1.00  --include_path                          ""
% 3.00/1.00  --clausifier                            res/vclausify_rel
% 3.00/1.00  --clausifier_options                    --mode clausify
% 3.00/1.00  --stdin                                 false
% 3.00/1.00  --stats_out                             all
% 3.00/1.00  
% 3.00/1.00  ------ General Options
% 3.00/1.00  
% 3.00/1.00  --fof                                   false
% 3.00/1.00  --time_out_real                         305.
% 3.00/1.00  --time_out_virtual                      -1.
% 3.00/1.00  --symbol_type_check                     false
% 3.00/1.00  --clausify_out                          false
% 3.00/1.00  --sig_cnt_out                           false
% 3.00/1.00  --trig_cnt_out                          false
% 3.00/1.00  --trig_cnt_out_tolerance                1.
% 3.00/1.00  --trig_cnt_out_sk_spl                   false
% 3.00/1.00  --abstr_cl_out                          false
% 3.00/1.00  
% 3.00/1.00  ------ Global Options
% 3.00/1.00  
% 3.00/1.00  --schedule                              default
% 3.00/1.00  --add_important_lit                     false
% 3.00/1.00  --prop_solver_per_cl                    1000
% 3.00/1.00  --min_unsat_core                        false
% 3.00/1.00  --soft_assumptions                      false
% 3.00/1.00  --soft_lemma_size                       3
% 3.00/1.00  --prop_impl_unit_size                   0
% 3.00/1.00  --prop_impl_unit                        []
% 3.00/1.00  --share_sel_clauses                     true
% 3.00/1.00  --reset_solvers                         false
% 3.00/1.00  --bc_imp_inh                            [conj_cone]
% 3.00/1.00  --conj_cone_tolerance                   3.
% 3.00/1.00  --extra_neg_conj                        none
% 3.00/1.00  --large_theory_mode                     true
% 3.00/1.00  --prolific_symb_bound                   200
% 3.00/1.00  --lt_threshold                          2000
% 3.00/1.00  --clause_weak_htbl                      true
% 3.00/1.00  --gc_record_bc_elim                     false
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing Options
% 3.00/1.00  
% 3.00/1.00  --preprocessing_flag                    true
% 3.00/1.00  --time_out_prep_mult                    0.1
% 3.00/1.00  --splitting_mode                        input
% 3.00/1.00  --splitting_grd                         true
% 3.00/1.00  --splitting_cvd                         false
% 3.00/1.00  --splitting_cvd_svl                     false
% 3.00/1.00  --splitting_nvd                         32
% 3.00/1.00  --sub_typing                            true
% 3.00/1.00  --prep_gs_sim                           true
% 3.00/1.00  --prep_unflatten                        true
% 3.00/1.00  --prep_res_sim                          true
% 3.00/1.00  --prep_upred                            true
% 3.00/1.00  --prep_sem_filter                       exhaustive
% 3.00/1.00  --prep_sem_filter_out                   false
% 3.00/1.00  --pred_elim                             true
% 3.00/1.00  --res_sim_input                         true
% 3.00/1.00  --eq_ax_congr_red                       true
% 3.00/1.00  --pure_diseq_elim                       true
% 3.00/1.00  --brand_transform                       false
% 3.00/1.00  --non_eq_to_eq                          false
% 3.00/1.00  --prep_def_merge                        true
% 3.00/1.00  --prep_def_merge_prop_impl              false
% 3.00/1.00  --prep_def_merge_mbd                    true
% 3.00/1.00  --prep_def_merge_tr_red                 false
% 3.00/1.00  --prep_def_merge_tr_cl                  false
% 3.00/1.00  --smt_preprocessing                     true
% 3.00/1.00  --smt_ac_axioms                         fast
% 3.00/1.00  --preprocessed_out                      false
% 3.00/1.00  --preprocessed_stats                    false
% 3.00/1.00  
% 3.00/1.00  ------ Abstraction refinement Options
% 3.00/1.00  
% 3.00/1.00  --abstr_ref                             []
% 3.00/1.00  --abstr_ref_prep                        false
% 3.00/1.00  --abstr_ref_until_sat                   false
% 3.00/1.00  --abstr_ref_sig_restrict                funpre
% 3.00/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.00  --abstr_ref_under                       []
% 3.00/1.00  
% 3.00/1.00  ------ SAT Options
% 3.00/1.00  
% 3.00/1.00  --sat_mode                              false
% 3.00/1.00  --sat_fm_restart_options                ""
% 3.00/1.00  --sat_gr_def                            false
% 3.00/1.00  --sat_epr_types                         true
% 3.00/1.00  --sat_non_cyclic_types                  false
% 3.00/1.00  --sat_finite_models                     false
% 3.00/1.00  --sat_fm_lemmas                         false
% 3.00/1.00  --sat_fm_prep                           false
% 3.00/1.00  --sat_fm_uc_incr                        true
% 3.00/1.00  --sat_out_model                         small
% 3.00/1.00  --sat_out_clauses                       false
% 3.00/1.00  
% 3.00/1.00  ------ QBF Options
% 3.00/1.00  
% 3.00/1.00  --qbf_mode                              false
% 3.00/1.00  --qbf_elim_univ                         false
% 3.00/1.00  --qbf_dom_inst                          none
% 3.00/1.00  --qbf_dom_pre_inst                      false
% 3.00/1.00  --qbf_sk_in                             false
% 3.00/1.00  --qbf_pred_elim                         true
% 3.00/1.00  --qbf_split                             512
% 3.00/1.00  
% 3.00/1.00  ------ BMC1 Options
% 3.00/1.00  
% 3.00/1.00  --bmc1_incremental                      false
% 3.00/1.00  --bmc1_axioms                           reachable_all
% 3.00/1.00  --bmc1_min_bound                        0
% 3.00/1.00  --bmc1_max_bound                        -1
% 3.00/1.00  --bmc1_max_bound_default                -1
% 3.00/1.00  --bmc1_symbol_reachability              true
% 3.00/1.00  --bmc1_property_lemmas                  false
% 3.00/1.00  --bmc1_k_induction                      false
% 3.00/1.00  --bmc1_non_equiv_states                 false
% 3.00/1.00  --bmc1_deadlock                         false
% 3.00/1.00  --bmc1_ucm                              false
% 3.00/1.00  --bmc1_add_unsat_core                   none
% 3.00/1.00  --bmc1_unsat_core_children              false
% 3.00/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.00  --bmc1_out_stat                         full
% 3.00/1.00  --bmc1_ground_init                      false
% 3.00/1.00  --bmc1_pre_inst_next_state              false
% 3.00/1.00  --bmc1_pre_inst_state                   false
% 3.00/1.00  --bmc1_pre_inst_reach_state             false
% 3.00/1.00  --bmc1_out_unsat_core                   false
% 3.00/1.00  --bmc1_aig_witness_out                  false
% 3.00/1.00  --bmc1_verbose                          false
% 3.00/1.00  --bmc1_dump_clauses_tptp                false
% 3.00/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.00  --bmc1_dump_file                        -
% 3.00/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.00  --bmc1_ucm_extend_mode                  1
% 3.00/1.00  --bmc1_ucm_init_mode                    2
% 3.00/1.00  --bmc1_ucm_cone_mode                    none
% 3.00/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.00  --bmc1_ucm_relax_model                  4
% 3.00/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.00  --bmc1_ucm_layered_model                none
% 3.00/1.00  --bmc1_ucm_max_lemma_size               10
% 3.00/1.00  
% 3.00/1.00  ------ AIG Options
% 3.00/1.00  
% 3.00/1.00  --aig_mode                              false
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation Options
% 3.00/1.00  
% 3.00/1.00  --instantiation_flag                    true
% 3.00/1.00  --inst_sos_flag                         false
% 3.00/1.00  --inst_sos_phase                        true
% 3.00/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.00  --inst_lit_sel_side                     none
% 3.00/1.00  --inst_solver_per_active                1400
% 3.00/1.00  --inst_solver_calls_frac                1.
% 3.00/1.00  --inst_passive_queue_type               priority_queues
% 3.00/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.00  --inst_passive_queues_freq              [25;2]
% 3.00/1.00  --inst_dismatching                      true
% 3.00/1.00  --inst_eager_unprocessed_to_passive     true
% 3.00/1.00  --inst_prop_sim_given                   true
% 3.00/1.00  --inst_prop_sim_new                     false
% 3.00/1.00  --inst_subs_new                         false
% 3.00/1.00  --inst_eq_res_simp                      false
% 3.00/1.00  --inst_subs_given                       false
% 3.00/1.00  --inst_orphan_elimination               true
% 3.00/1.00  --inst_learning_loop_flag               true
% 3.00/1.00  --inst_learning_start                   3000
% 3.00/1.00  --inst_learning_factor                  2
% 3.00/1.00  --inst_start_prop_sim_after_learn       3
% 3.00/1.00  --inst_sel_renew                        solver
% 3.00/1.00  --inst_lit_activity_flag                true
% 3.00/1.00  --inst_restr_to_given                   false
% 3.00/1.00  --inst_activity_threshold               500
% 3.00/1.00  --inst_out_proof                        true
% 3.00/1.00  
% 3.00/1.00  ------ Resolution Options
% 3.00/1.00  
% 3.00/1.00  --resolution_flag                       false
% 3.00/1.00  --res_lit_sel                           adaptive
% 3.00/1.00  --res_lit_sel_side                      none
% 3.00/1.00  --res_ordering                          kbo
% 3.00/1.00  --res_to_prop_solver                    active
% 3.00/1.00  --res_prop_simpl_new                    false
% 3.00/1.00  --res_prop_simpl_given                  true
% 3.00/1.00  --res_passive_queue_type                priority_queues
% 3.00/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.00  --res_passive_queues_freq               [15;5]
% 3.00/1.00  --res_forward_subs                      full
% 3.00/1.00  --res_backward_subs                     full
% 3.00/1.00  --res_forward_subs_resolution           true
% 3.00/1.00  --res_backward_subs_resolution          true
% 3.00/1.00  --res_orphan_elimination                true
% 3.00/1.00  --res_time_limit                        2.
% 3.00/1.00  --res_out_proof                         true
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Options
% 3.00/1.00  
% 3.00/1.00  --superposition_flag                    true
% 3.00/1.00  --sup_passive_queue_type                priority_queues
% 3.00/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.00  --demod_completeness_check              fast
% 3.00/1.00  --demod_use_ground                      true
% 3.00/1.00  --sup_to_prop_solver                    passive
% 3.00/1.00  --sup_prop_simpl_new                    true
% 3.00/1.00  --sup_prop_simpl_given                  true
% 3.00/1.00  --sup_fun_splitting                     false
% 3.00/1.00  --sup_smt_interval                      50000
% 3.00/1.00  
% 3.00/1.00  ------ Superposition Simplification Setup
% 3.00/1.00  
% 3.00/1.00  --sup_indices_passive                   []
% 3.00/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_full_bw                           [BwDemod]
% 3.00/1.00  --sup_immed_triv                        [TrivRules]
% 3.00/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_immed_bw_main                     []
% 3.00/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.00  
% 3.00/1.00  ------ Combination Options
% 3.00/1.00  
% 3.00/1.00  --comb_res_mult                         3
% 3.00/1.00  --comb_sup_mult                         2
% 3.00/1.00  --comb_inst_mult                        10
% 3.00/1.00  
% 3.00/1.00  ------ Debug Options
% 3.00/1.00  
% 3.00/1.00  --dbg_backtrace                         false
% 3.00/1.00  --dbg_dump_prop_clauses                 false
% 3.00/1.00  --dbg_dump_prop_clauses_file            -
% 3.00/1.00  --dbg_out_stat                          false
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  ------ Proving...
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  % SZS status Theorem for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  fof(f12,axiom,(
% 3.00/1.00    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f40,plain,(
% 3.00/1.00    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK3(X0),X0))),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f41,plain,(
% 3.00/1.00    ! [X0] : m1_subset_1(sK3(X0),X0)),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f40])).
% 3.00/1.00  
% 3.00/1.00  fof(f62,plain,(
% 3.00/1.00    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f41])).
% 3.00/1.00  
% 3.00/1.00  fof(f13,axiom,(
% 3.00/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f63,plain,(
% 3.00/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f13])).
% 3.00/1.00  
% 3.00/1.00  fof(f11,axiom,(
% 3.00/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f24,plain,(
% 3.00/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.00/1.00    inference(ennf_transformation,[],[f11])).
% 3.00/1.00  
% 3.00/1.00  fof(f61,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f24])).
% 3.00/1.00  
% 3.00/1.00  fof(f3,axiom,(
% 3.00/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f49,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f3])).
% 3.00/1.00  
% 3.00/1.00  fof(f15,axiom,(
% 3.00/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f65,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.00/1.00    inference(cnf_transformation,[],[f15])).
% 3.00/1.00  
% 3.00/1.00  fof(f7,axiom,(
% 3.00/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f53,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f7])).
% 3.00/1.00  
% 3.00/1.00  fof(f8,axiom,(
% 3.00/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f54,plain,(
% 3.00/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f8])).
% 3.00/1.00  
% 3.00/1.00  fof(f70,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.00/1.00    inference(definition_unfolding,[],[f53,f54])).
% 3.00/1.00  
% 3.00/1.00  fof(f71,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 3.00/1.00    inference(definition_unfolding,[],[f65,f70])).
% 3.00/1.00  
% 3.00/1.00  fof(f72,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.00/1.00    inference(definition_unfolding,[],[f49,f71])).
% 3.00/1.00  
% 3.00/1.00  fof(f74,plain,(
% 3.00/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.00/1.00    inference(definition_unfolding,[],[f61,f72])).
% 3.00/1.00  
% 3.00/1.00  fof(f4,axiom,(
% 3.00/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f50,plain,(
% 3.00/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.00/1.00    inference(cnf_transformation,[],[f4])).
% 3.00/1.00  
% 3.00/1.00  fof(f73,plain,(
% 3.00/1.00    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) )),
% 3.00/1.00    inference(definition_unfolding,[],[f50,f71])).
% 3.00/1.00  
% 3.00/1.00  fof(f6,axiom,(
% 3.00/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f52,plain,(
% 3.00/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.00/1.00    inference(cnf_transformation,[],[f6])).
% 3.00/1.00  
% 3.00/1.00  fof(f14,axiom,(
% 3.00/1.00    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f25,plain,(
% 3.00/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 3.00/1.00    inference(ennf_transformation,[],[f14])).
% 3.00/1.00  
% 3.00/1.00  fof(f26,plain,(
% 3.00/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 3.00/1.00    inference(flattening,[],[f25])).
% 3.00/1.00  
% 3.00/1.00  fof(f64,plain,(
% 3.00/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 3.00/1.00    inference(cnf_transformation,[],[f26])).
% 3.00/1.00  
% 3.00/1.00  fof(f5,axiom,(
% 3.00/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f51,plain,(
% 3.00/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f5])).
% 3.00/1.00  
% 3.00/1.00  fof(f17,axiom,(
% 3.00/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f29,plain,(
% 3.00/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.00/1.00    inference(ennf_transformation,[],[f17])).
% 3.00/1.00  
% 3.00/1.00  fof(f67,plain,(
% 3.00/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f29])).
% 3.00/1.00  
% 3.00/1.00  fof(f2,axiom,(
% 3.00/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f20,plain,(
% 3.00/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.00/1.00    inference(rectify,[],[f2])).
% 3.00/1.00  
% 3.00/1.00  fof(f21,plain,(
% 3.00/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.00/1.00    inference(ennf_transformation,[],[f20])).
% 3.00/1.00  
% 3.00/1.00  fof(f35,plain,(
% 3.00/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f36,plain,(
% 3.00/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f35])).
% 3.00/1.00  
% 3.00/1.00  fof(f46,plain,(
% 3.00/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f36])).
% 3.00/1.00  
% 3.00/1.00  fof(f9,axiom,(
% 3.00/1.00    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f22,plain,(
% 3.00/1.00    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 3.00/1.00    inference(ennf_transformation,[],[f9])).
% 3.00/1.00  
% 3.00/1.00  fof(f37,plain,(
% 3.00/1.00    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f38,plain,(
% 3.00/1.00    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f37])).
% 3.00/1.00  
% 3.00/1.00  fof(f55,plain,(
% 3.00/1.00    ( ! [X0,X1] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X0,X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f38])).
% 3.00/1.00  
% 3.00/1.00  fof(f18,conjecture,(
% 3.00/1.00    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f19,negated_conjecture,(
% 3.00/1.00    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.00/1.00    inference(negated_conjecture,[],[f18])).
% 3.00/1.00  
% 3.00/1.00  fof(f30,plain,(
% 3.00/1.00    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.00/1.00    inference(ennf_transformation,[],[f19])).
% 3.00/1.00  
% 3.00/1.00  fof(f42,plain,(
% 3.00/1.00    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK4) | ~r2_hidden(X1,sK4)) & k1_xboole_0 != sK4)),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f43,plain,(
% 3.00/1.00    ! [X1] : (~r1_xboole_0(X1,sK4) | ~r2_hidden(X1,sK4)) & k1_xboole_0 != sK4),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f42])).
% 3.00/1.00  
% 3.00/1.00  fof(f69,plain,(
% 3.00/1.00    ( ! [X1] : (~r1_xboole_0(X1,sK4) | ~r2_hidden(X1,sK4)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f43])).
% 3.00/1.00  
% 3.00/1.00  fof(f10,axiom,(
% 3.00/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f23,plain,(
% 3.00/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.00/1.00    inference(ennf_transformation,[],[f10])).
% 3.00/1.00  
% 3.00/1.00  fof(f39,plain,(
% 3.00/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.00/1.00    inference(nnf_transformation,[],[f23])).
% 3.00/1.00  
% 3.00/1.00  fof(f58,plain,(
% 3.00/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f39])).
% 3.00/1.00  
% 3.00/1.00  fof(f1,axiom,(
% 3.00/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.00  
% 3.00/1.00  fof(f31,plain,(
% 3.00/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.00    inference(nnf_transformation,[],[f1])).
% 3.00/1.00  
% 3.00/1.00  fof(f32,plain,(
% 3.00/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.00    inference(rectify,[],[f31])).
% 3.00/1.00  
% 3.00/1.00  fof(f33,plain,(
% 3.00/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.00/1.00    introduced(choice_axiom,[])).
% 3.00/1.00  
% 3.00/1.00  fof(f34,plain,(
% 3.00/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 3.00/1.00  
% 3.00/1.00  fof(f44,plain,(
% 3.00/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f34])).
% 3.00/1.00  
% 3.00/1.00  fof(f45,plain,(
% 3.00/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f34])).
% 3.00/1.00  
% 3.00/1.00  fof(f59,plain,(
% 3.00/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f39])).
% 3.00/1.00  
% 3.00/1.00  fof(f47,plain,(
% 3.00/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f36])).
% 3.00/1.00  
% 3.00/1.00  fof(f56,plain,(
% 3.00/1.00    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 3.00/1.00    inference(cnf_transformation,[],[f38])).
% 3.00/1.00  
% 3.00/1.00  fof(f68,plain,(
% 3.00/1.00    k1_xboole_0 != sK4),
% 3.00/1.00    inference(cnf_transformation,[],[f43])).
% 3.00/1.00  
% 3.00/1.00  cnf(c_15,plain,
% 3.00/1.00      ( m1_subset_1(sK3(X0),X0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_813,plain,
% 3.00/1.00      ( m1_subset_1(sK3(X0),X0) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_16,plain,
% 3.00/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.00/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_812,plain,
% 3.00/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_14,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/1.00      | k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_814,plain,
% 3.00/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k3_subset_1(X0,X1)
% 3.00/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1857,plain,
% 3.00/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_812,c_814]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_5,plain,
% 3.00/1.00      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.00/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_7,plain,
% 3.00/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.00/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1859,plain,
% 3.00/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.00/1.00      inference(light_normalisation,[status(thm)],[c_1857,c_5,c_7]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_17,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,X1)
% 3.00/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.00/1.00      | r2_hidden(X0,X2)
% 3.00/1.00      | r2_hidden(X0,k3_subset_1(X1,X2))
% 3.00/1.00      | k1_xboole_0 = X1 ),
% 3.00/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_811,plain,
% 3.00/1.00      ( k1_xboole_0 = X0
% 3.00/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.00/1.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.00/1.00      | r2_hidden(X1,X2) = iProver_top
% 3.00/1.00      | r2_hidden(X1,k3_subset_1(X0,X2)) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2292,plain,
% 3.00/1.00      ( k1_xboole_0 = X0
% 3.00/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.00/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
% 3.00/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.00/1.00      | r2_hidden(X1,k1_xboole_0) = iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_1859,c_811]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_34,plain,
% 3.00/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6084,plain,
% 3.00/1.00      ( m1_subset_1(X1,X0) != iProver_top
% 3.00/1.00      | k1_xboole_0 = X0
% 3.00/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.00/1.00      | r2_hidden(X1,k1_xboole_0) = iProver_top ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_2292,c_34]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6085,plain,
% 3.00/1.00      ( k1_xboole_0 = X0
% 3.00/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.00/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.00/1.00      | r2_hidden(X1,k1_xboole_0) = iProver_top ),
% 3.00/1.00      inference(renaming,[status(thm)],[c_6084]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6,plain,
% 3.00/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_19,plain,
% 3.00/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_235,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.00/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_236,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.00/1.00      inference(unflattening,[status(thm)],[c_235]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_807,plain,
% 3.00/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6092,plain,
% 3.00/1.00      ( k1_xboole_0 = X0
% 3.00/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.00/1.00      | r2_hidden(X1,X0) = iProver_top ),
% 3.00/1.00      inference(forward_subsumption_resolution,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_6085,c_807]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6095,plain,
% 3.00/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0) = iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_813,c_6092]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_4,plain,
% 3.00/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_820,plain,
% 3.00/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 3.00/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_9,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1) ),
% 3.00/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_818,plain,
% 3.00/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.00/1.00      | r2_hidden(sK2(X1),X1) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1285,plain,
% 3.00/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 3.00/1.00      | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_820,c_818]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_20,negated_conjecture,
% 3.00/1.00      ( ~ r1_xboole_0(X0,sK4) | ~ r2_hidden(X0,sK4) ),
% 3.00/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_809,plain,
% 3.00/1.00      ( r1_xboole_0(X0,sK4) != iProver_top
% 3.00/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3200,plain,
% 3.00/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.00/1.00      | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_1285,c_809]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_12,plain,
% 3.00/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.00/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.00/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_124,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_12,c_1]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_125,plain,
% 3.00/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.00/1.00      inference(renaming,[status(thm)],[c_124]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_991,plain,
% 3.00/1.00      ( m1_subset_1(X0,sK4) | ~ r2_hidden(X0,sK4) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_125]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_992,plain,
% 3.00/1.00      ( m1_subset_1(X0,sK4) = iProver_top
% 3.00/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_991]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_0,plain,
% 3.00/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1017,plain,
% 3.00/1.00      ( r2_hidden(sK0(sK4),sK4) | v1_xboole_0(sK4) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1018,plain,
% 3.00/1.00      ( r2_hidden(sK0(sK4),sK4) = iProver_top
% 3.00/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1017]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1076,plain,
% 3.00/1.00      ( r2_hidden(sK2(sK4),sK4) | ~ r2_hidden(sK0(sK4),sK4) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1080,plain,
% 3.00/1.00      ( r2_hidden(sK2(sK4),sK4) = iProver_top
% 3.00/1.00      | r2_hidden(sK0(sK4),sK4) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1076]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_11,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.00/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1249,plain,
% 3.00/1.00      ( ~ m1_subset_1(X0,sK4) | v1_xboole_0(X0) | ~ v1_xboole_0(sK4) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1250,plain,
% 3.00/1.00      ( m1_subset_1(X0,sK4) != iProver_top
% 3.00/1.00      | v1_xboole_0(X0) = iProver_top
% 3.00/1.00      | v1_xboole_0(sK4) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1249]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_823,plain,
% 3.00/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.00/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1286,plain,
% 3.00/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 3.00/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_820,c_823]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1537,plain,
% 3.00/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.00/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_1286,c_809]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1666,plain,
% 3.00/1.00      ( ~ r1_xboole_0(sK2(sK4),sK4) | ~ r2_hidden(sK2(sK4),sK4) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_1667,plain,
% 3.00/1.00      ( r1_xboole_0(sK2(sK4),sK4) != iProver_top
% 3.00/1.00      | r2_hidden(sK2(sK4),sK4) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1666]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3,plain,
% 3.00/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 3.00/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_958,plain,
% 3.00/1.00      ( r1_xboole_0(X0,sK4) | r2_hidden(sK1(X0,sK4),sK4) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2117,plain,
% 3.00/1.00      ( r1_xboole_0(sK2(sK4),sK4) | r2_hidden(sK1(sK2(sK4),sK4),sK4) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_958]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2118,plain,
% 3.00/1.00      ( r1_xboole_0(sK2(sK4),sK4) = iProver_top
% 3.00/1.00      | r2_hidden(sK1(sK2(sK4),sK4),sK4) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_2117]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_963,plain,
% 3.00/1.00      ( r1_xboole_0(X0,sK4) | r2_hidden(sK1(X0,sK4),X0) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2116,plain,
% 3.00/1.00      ( r1_xboole_0(sK2(sK4),sK4)
% 3.00/1.00      | r2_hidden(sK1(sK2(sK4),sK4),sK2(sK4)) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_963]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2120,plain,
% 3.00/1.00      ( r1_xboole_0(sK2(sK4),sK4) = iProver_top
% 3.00/1.00      | r2_hidden(sK1(sK2(sK4),sK4),sK2(sK4)) = iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_2116]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_8,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,X1)
% 3.00/1.00      | ~ r2_hidden(X2,X1)
% 3.00/1.00      | ~ r2_hidden(X0,sK2(X1)) ),
% 3.00/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2622,plain,
% 3.00/1.00      ( ~ r2_hidden(X0,sK4)
% 3.00/1.00      | ~ r2_hidden(sK1(sK2(sK4),sK4),sK2(sK4))
% 3.00/1.00      | ~ r2_hidden(sK1(sK2(sK4),sK4),sK4) ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_2629,plain,
% 3.00/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.00/1.00      | r2_hidden(sK1(sK2(sK4),sK4),sK2(sK4)) != iProver_top
% 3.00/1.00      | r2_hidden(sK1(sK2(sK4),sK4),sK4) != iProver_top ),
% 3.00/1.00      inference(predicate_to_equality,[status(thm)],[c_2622]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_3775,plain,
% 3.00/1.00      ( r2_hidden(X0,sK4) != iProver_top ),
% 3.00/1.00      inference(global_propositional_subsumption,
% 3.00/1.00                [status(thm)],
% 3.00/1.00                [c_3200,c_992,c_1018,c_1080,c_1250,c_1537,c_1667,c_2118,
% 3.00/1.00                 c_2120,c_2629]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_6167,plain,
% 3.00/1.00      ( sK4 = k1_xboole_0 ),
% 3.00/1.00      inference(superposition,[status(thm)],[c_6095,c_3775]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_485,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_968,plain,
% 3.00/1.00      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_485]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_969,plain,
% 3.00/1.00      ( sK4 != k1_xboole_0
% 3.00/1.00      | k1_xboole_0 = sK4
% 3.00/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_968]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_484,plain,( X0 = X0 ),theory(equality) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_499,plain,
% 3.00/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.00/1.00      inference(instantiation,[status(thm)],[c_484]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(c_21,negated_conjecture,
% 3.00/1.00      ( k1_xboole_0 != sK4 ),
% 3.00/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.00/1.00  
% 3.00/1.00  cnf(contradiction,plain,
% 3.00/1.00      ( $false ),
% 3.00/1.00      inference(minisat,[status(thm)],[c_6167,c_969,c_499,c_21]) ).
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  ------                               Statistics
% 3.00/1.00  
% 3.00/1.00  ------ General
% 3.00/1.00  
% 3.00/1.00  abstr_ref_over_cycles:                  0
% 3.00/1.00  abstr_ref_under_cycles:                 0
% 3.00/1.00  gc_basic_clause_elim:                   0
% 3.00/1.00  forced_gc_time:                         0
% 3.00/1.00  parsing_time:                           0.009
% 3.00/1.00  unif_index_cands_time:                  0.
% 3.00/1.00  unif_index_add_time:                    0.
% 3.00/1.00  orderings_time:                         0.
% 3.00/1.00  out_proof_time:                         0.01
% 3.00/1.00  total_time:                             0.191
% 3.00/1.00  num_of_symbols:                         47
% 3.00/1.00  num_of_terms:                           4863
% 3.00/1.00  
% 3.00/1.00  ------ Preprocessing
% 3.00/1.00  
% 3.00/1.00  num_of_splits:                          0
% 3.00/1.00  num_of_split_atoms:                     0
% 3.00/1.00  num_of_reused_defs:                     0
% 3.00/1.00  num_eq_ax_congr_red:                    43
% 3.00/1.00  num_of_sem_filtered_clauses:            1
% 3.00/1.00  num_of_subtypes:                        0
% 3.00/1.00  monotx_restored_types:                  0
% 3.00/1.00  sat_num_of_epr_types:                   0
% 3.00/1.00  sat_num_of_non_cyclic_types:            0
% 3.00/1.00  sat_guarded_non_collapsed_types:        0
% 3.00/1.00  num_pure_diseq_elim:                    0
% 3.00/1.00  simp_replaced_by:                       0
% 3.00/1.00  res_preprocessed:                       102
% 3.00/1.00  prep_upred:                             0
% 3.00/1.00  prep_unflattend:                        10
% 3.00/1.00  smt_new_axioms:                         0
% 3.00/1.00  pred_elim_cands:                        4
% 3.00/1.00  pred_elim:                              1
% 3.00/1.00  pred_elim_cl:                           1
% 3.00/1.00  pred_elim_cycles:                       3
% 3.00/1.00  merged_defs:                            0
% 3.00/1.00  merged_defs_ncl:                        0
% 3.00/1.00  bin_hyper_res:                          0
% 3.00/1.00  prep_cycles:                            4
% 3.00/1.00  pred_elim_time:                         0.002
% 3.00/1.00  splitting_time:                         0.
% 3.00/1.00  sem_filter_time:                        0.
% 3.00/1.00  monotx_time:                            0.
% 3.00/1.00  subtype_inf_time:                       0.
% 3.00/1.00  
% 3.00/1.00  ------ Problem properties
% 3.00/1.00  
% 3.00/1.00  clauses:                                21
% 3.00/1.00  conjectures:                            2
% 3.00/1.00  epr:                                    9
% 3.00/1.00  horn:                                   16
% 3.00/1.00  ground:                                 1
% 3.00/1.00  unary:                                  6
% 3.00/1.00  binary:                                 8
% 3.00/1.00  lits:                                   45
% 3.00/1.00  lits_eq:                                5
% 3.00/1.00  fd_pure:                                0
% 3.00/1.00  fd_pseudo:                              0
% 3.00/1.00  fd_cond:                                1
% 3.00/1.00  fd_pseudo_cond:                         0
% 3.00/1.00  ac_symbols:                             0
% 3.00/1.00  
% 3.00/1.00  ------ Propositional Solver
% 3.00/1.00  
% 3.00/1.00  prop_solver_calls:                      30
% 3.00/1.00  prop_fast_solver_calls:                 667
% 3.00/1.00  smt_solver_calls:                       0
% 3.00/1.00  smt_fast_solver_calls:                  0
% 3.00/1.00  prop_num_of_clauses:                    2460
% 3.00/1.00  prop_preprocess_simplified:             6667
% 3.00/1.00  prop_fo_subsumed:                       3
% 3.00/1.00  prop_solver_time:                       0.
% 3.00/1.00  smt_solver_time:                        0.
% 3.00/1.00  smt_fast_solver_time:                   0.
% 3.00/1.00  prop_fast_solver_time:                  0.
% 3.00/1.00  prop_unsat_core_time:                   0.
% 3.00/1.00  
% 3.00/1.00  ------ QBF
% 3.00/1.00  
% 3.00/1.00  qbf_q_res:                              0
% 3.00/1.00  qbf_num_tautologies:                    0
% 3.00/1.00  qbf_prep_cycles:                        0
% 3.00/1.00  
% 3.00/1.00  ------ BMC1
% 3.00/1.00  
% 3.00/1.00  bmc1_current_bound:                     -1
% 3.00/1.00  bmc1_last_solved_bound:                 -1
% 3.00/1.00  bmc1_unsat_core_size:                   -1
% 3.00/1.00  bmc1_unsat_core_parents_size:           -1
% 3.00/1.00  bmc1_merge_next_fun:                    0
% 3.00/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.00  
% 3.00/1.00  ------ Instantiation
% 3.00/1.00  
% 3.00/1.00  inst_num_of_clauses:                    658
% 3.00/1.00  inst_num_in_passive:                    213
% 3.00/1.00  inst_num_in_active:                     294
% 3.00/1.00  inst_num_in_unprocessed:                153
% 3.00/1.00  inst_num_of_loops:                      420
% 3.00/1.00  inst_num_of_learning_restarts:          0
% 3.00/1.00  inst_num_moves_active_passive:          121
% 3.00/1.00  inst_lit_activity:                      0
% 3.00/1.00  inst_lit_activity_moves:                0
% 3.00/1.00  inst_num_tautologies:                   0
% 3.00/1.00  inst_num_prop_implied:                  0
% 3.00/1.00  inst_num_existing_simplified:           0
% 3.00/1.00  inst_num_eq_res_simplified:             0
% 3.00/1.00  inst_num_child_elim:                    0
% 3.00/1.00  inst_num_of_dismatching_blockings:      223
% 3.00/1.00  inst_num_of_non_proper_insts:           594
% 3.00/1.00  inst_num_of_duplicates:                 0
% 3.00/1.00  inst_inst_num_from_inst_to_res:         0
% 3.00/1.00  inst_dismatching_checking_time:         0.
% 3.00/1.00  
% 3.00/1.00  ------ Resolution
% 3.00/1.00  
% 3.00/1.00  res_num_of_clauses:                     0
% 3.00/1.00  res_num_in_passive:                     0
% 3.00/1.00  res_num_in_active:                      0
% 3.00/1.00  res_num_of_loops:                       106
% 3.00/1.00  res_forward_subset_subsumed:            38
% 3.00/1.00  res_backward_subset_subsumed:           4
% 3.00/1.00  res_forward_subsumed:                   0
% 3.00/1.00  res_backward_subsumed:                  0
% 3.00/1.00  res_forward_subsumption_resolution:     0
% 3.00/1.00  res_backward_subsumption_resolution:    0
% 3.00/1.00  res_clause_to_clause_subsumption:       558
% 3.00/1.00  res_orphan_elimination:                 0
% 3.00/1.00  res_tautology_del:                      28
% 3.00/1.00  res_num_eq_res_simplified:              0
% 3.00/1.00  res_num_sel_changes:                    0
% 3.00/1.00  res_moves_from_active_to_pass:          0
% 3.00/1.00  
% 3.00/1.00  ------ Superposition
% 3.00/1.00  
% 3.00/1.00  sup_time_total:                         0.
% 3.00/1.00  sup_time_generating:                    0.
% 3.00/1.00  sup_time_sim_full:                      0.
% 3.00/1.00  sup_time_sim_immed:                     0.
% 3.00/1.00  
% 3.00/1.00  sup_num_of_clauses:                     154
% 3.00/1.00  sup_num_in_active:                      79
% 3.00/1.00  sup_num_in_passive:                     75
% 3.00/1.00  sup_num_of_loops:                       83
% 3.00/1.00  sup_fw_superposition:                   129
% 3.00/1.00  sup_bw_superposition:                   126
% 3.00/1.00  sup_immediate_simplified:               38
% 3.00/1.00  sup_given_eliminated:                   0
% 3.00/1.00  comparisons_done:                       0
% 3.00/1.00  comparisons_avoided:                    0
% 3.00/1.00  
% 3.00/1.00  ------ Simplifications
% 3.00/1.00  
% 3.00/1.00  
% 3.00/1.00  sim_fw_subset_subsumed:                 21
% 3.00/1.00  sim_bw_subset_subsumed:                 10
% 3.00/1.00  sim_fw_subsumed:                        14
% 3.00/1.00  sim_bw_subsumed:                        2
% 3.00/1.00  sim_fw_subsumption_res:                 2
% 3.00/1.00  sim_bw_subsumption_res:                 0
% 3.00/1.00  sim_tautology_del:                      10
% 3.00/1.00  sim_eq_tautology_del:                   1
% 3.00/1.00  sim_eq_res_simp:                        0
% 3.00/1.00  sim_fw_demodulated:                     0
% 3.00/1.00  sim_bw_demodulated:                     0
% 3.00/1.00  sim_light_normalised:                   1
% 3.00/1.00  sim_joinable_taut:                      0
% 3.00/1.00  sim_joinable_simp:                      0
% 3.00/1.00  sim_ac_normalised:                      0
% 3.00/1.00  sim_smt_subsumption:                    0
% 3.00/1.00  
%------------------------------------------------------------------------------
