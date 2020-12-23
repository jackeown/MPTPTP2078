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
% DateTime   : Thu Dec  3 11:43:13 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 212 expanded)
%              Number of clauses        :   56 (  70 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  343 ( 729 expanded)
%              Number of equality atoms :   88 ( 120 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK3))
        & r1_tarski(X0,sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(X1))
          & r1_tarski(sK2,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f38,f37])).

fof(f62,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f54,f52])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_779,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_782,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1403,plain,
    ( k2_xboole_0(k1_relat_1(sK3),k2_relat_1(sK3)) = k3_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_779,c_782])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_796,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_780,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_236,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_16,c_14])).

cnf(c_237,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_776,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_787,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_824,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_787,c_13])).

cnf(c_2202,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_824])).

cnf(c_12279,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),k1_relat_1(sK3))) = k1_relat_1(sK2)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_2202])).

cnf(c_25,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13373,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),k1_relat_1(sK3))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12279,c_25])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_790,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2371,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_790])).

cnf(c_13380,plain,
    ( r2_hidden(X0,k4_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13373,c_2371])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_789,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14925,plain,
    ( r2_hidden(X0,k4_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13380,c_789])).

cnf(c_14929,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_796,c_14925])).

cnf(c_11,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_786,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_22264,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_xboole_0(k1_relat_1(sK3),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14929,c_786])).

cnf(c_25593,plain,
    ( r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_22264])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_243,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_16,c_14])).

cnf(c_244,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_243])).

cnf(c_775,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_244])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_788,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1783,plain,
    ( r1_tarski(X0,k3_relat_1(sK3)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_788])).

cnf(c_1999,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_1783])).

cnf(c_2597,plain,
    ( r1_tarski(k2_relat_1(X0),k3_relat_1(sK3)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1999,c_25])).

cnf(c_2598,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2597])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_778,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1404,plain,
    ( k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) = k3_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_778,c_782])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_785,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5218,plain,
    ( r1_tarski(k3_relat_1(sK2),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_785])).

cnf(c_6586,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) = iProver_top
    | r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2598,c_5218])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_26,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25593,c_6586,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:40:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.66/1.55  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/1.55  
% 7.66/1.55  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.66/1.55  
% 7.66/1.55  ------  iProver source info
% 7.66/1.55  
% 7.66/1.55  git: date: 2020-06-30 10:37:57 +0100
% 7.66/1.55  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.66/1.55  git: non_committed_changes: false
% 7.66/1.55  git: last_make_outside_of_git: false
% 7.66/1.55  
% 7.66/1.55  ------ 
% 7.66/1.55  ------ Parsing...
% 7.66/1.55  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.66/1.55  
% 7.66/1.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.66/1.55  
% 7.66/1.55  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.66/1.55  
% 7.66/1.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.66/1.55  ------ Proving...
% 7.66/1.55  ------ Problem Properties 
% 7.66/1.55  
% 7.66/1.55  
% 7.66/1.55  clauses                                 24
% 7.66/1.55  conjectures                             4
% 7.66/1.55  EPR                                     5
% 7.66/1.55  Horn                                    19
% 7.66/1.55  unary                                   5
% 7.66/1.55  binary                                  10
% 7.66/1.55  lits                                    53
% 7.66/1.55  lits eq                                 6
% 7.66/1.55  fd_pure                                 0
% 7.66/1.55  fd_pseudo                               0
% 7.66/1.55  fd_cond                                 0
% 7.66/1.55  fd_pseudo_cond                          3
% 7.66/1.55  AC symbols                              0
% 7.66/1.55  
% 7.66/1.55  ------ Input Options Time Limit: Unbounded
% 7.66/1.55  
% 7.66/1.55  
% 7.66/1.55  ------ 
% 7.66/1.55  Current options:
% 7.66/1.55  ------ 
% 7.66/1.55  
% 7.66/1.55  
% 7.66/1.55  
% 7.66/1.55  
% 7.66/1.55  ------ Proving...
% 7.66/1.55  
% 7.66/1.55  
% 7.66/1.55  % SZS status Theorem for theBenchmark.p
% 7.66/1.55  
% 7.66/1.55  % SZS output start CNFRefutation for theBenchmark.p
% 7.66/1.55  
% 7.66/1.55  fof(f13,conjecture,(
% 7.66/1.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f14,negated_conjecture,(
% 7.66/1.55    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 7.66/1.55    inference(negated_conjecture,[],[f13])).
% 7.66/1.55  
% 7.66/1.55  fof(f25,plain,(
% 7.66/1.55    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.66/1.55    inference(ennf_transformation,[],[f14])).
% 7.66/1.55  
% 7.66/1.55  fof(f26,plain,(
% 7.66/1.55    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.66/1.55    inference(flattening,[],[f25])).
% 7.66/1.55  
% 7.66/1.55  fof(f38,plain,(
% 7.66/1.55    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK3)) & r1_tarski(X0,sK3) & v1_relat_1(sK3))) )),
% 7.66/1.55    introduced(choice_axiom,[])).
% 7.66/1.55  
% 7.66/1.55  fof(f37,plain,(
% 7.66/1.55    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK2),k3_relat_1(X1)) & r1_tarski(sK2,X1) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 7.66/1.55    introduced(choice_axiom,[])).
% 7.66/1.55  
% 7.66/1.55  fof(f39,plain,(
% 7.66/1.55    (~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 7.66/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f38,f37])).
% 7.66/1.55  
% 7.66/1.55  fof(f62,plain,(
% 7.66/1.55    v1_relat_1(sK3)),
% 7.66/1.55    inference(cnf_transformation,[],[f39])).
% 7.66/1.55  
% 7.66/1.55  fof(f11,axiom,(
% 7.66/1.55    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f22,plain,(
% 7.66/1.55    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 7.66/1.55    inference(ennf_transformation,[],[f11])).
% 7.66/1.55  
% 7.66/1.55  fof(f58,plain,(
% 7.66/1.55    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.66/1.55    inference(cnf_transformation,[],[f22])).
% 7.66/1.55  
% 7.66/1.55  fof(f1,axiom,(
% 7.66/1.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f15,plain,(
% 7.66/1.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.66/1.55    inference(ennf_transformation,[],[f1])).
% 7.66/1.55  
% 7.66/1.55  fof(f27,plain,(
% 7.66/1.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.66/1.55    inference(nnf_transformation,[],[f15])).
% 7.66/1.55  
% 7.66/1.55  fof(f28,plain,(
% 7.66/1.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.66/1.55    inference(rectify,[],[f27])).
% 7.66/1.55  
% 7.66/1.55  fof(f29,plain,(
% 7.66/1.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.66/1.55    introduced(choice_axiom,[])).
% 7.66/1.55  
% 7.66/1.55  fof(f30,plain,(
% 7.66/1.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.66/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 7.66/1.55  
% 7.66/1.55  fof(f41,plain,(
% 7.66/1.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.66/1.55    inference(cnf_transformation,[],[f30])).
% 7.66/1.55  
% 7.66/1.55  fof(f63,plain,(
% 7.66/1.55    r1_tarski(sK2,sK3)),
% 7.66/1.55    inference(cnf_transformation,[],[f39])).
% 7.66/1.55  
% 7.66/1.55  fof(f12,axiom,(
% 7.66/1.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f23,plain,(
% 7.66/1.55    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.66/1.55    inference(ennf_transformation,[],[f12])).
% 7.66/1.55  
% 7.66/1.55  fof(f24,plain,(
% 7.66/1.55    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.66/1.55    inference(flattening,[],[f23])).
% 7.66/1.55  
% 7.66/1.55  fof(f59,plain,(
% 7.66/1.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.66/1.55    inference(cnf_transformation,[],[f24])).
% 7.66/1.55  
% 7.66/1.55  fof(f10,axiom,(
% 7.66/1.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f21,plain,(
% 7.66/1.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.66/1.55    inference(ennf_transformation,[],[f10])).
% 7.66/1.55  
% 7.66/1.55  fof(f57,plain,(
% 7.66/1.55    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.66/1.55    inference(cnf_transformation,[],[f21])).
% 7.66/1.55  
% 7.66/1.55  fof(f9,axiom,(
% 7.66/1.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f36,plain,(
% 7.66/1.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.66/1.55    inference(nnf_transformation,[],[f9])).
% 7.66/1.55  
% 7.66/1.55  fof(f56,plain,(
% 7.66/1.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.66/1.55    inference(cnf_transformation,[],[f36])).
% 7.66/1.55  
% 7.66/1.55  fof(f4,axiom,(
% 7.66/1.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f17,plain,(
% 7.66/1.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.66/1.55    inference(ennf_transformation,[],[f4])).
% 7.66/1.55  
% 7.66/1.55  fof(f50,plain,(
% 7.66/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.66/1.55    inference(cnf_transformation,[],[f17])).
% 7.66/1.55  
% 7.66/1.55  fof(f6,axiom,(
% 7.66/1.55    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f52,plain,(
% 7.66/1.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.66/1.55    inference(cnf_transformation,[],[f6])).
% 7.66/1.55  
% 7.66/1.55  fof(f65,plain,(
% 7.66/1.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.66/1.55    inference(definition_unfolding,[],[f50,f52])).
% 7.66/1.55  
% 7.66/1.55  fof(f8,axiom,(
% 7.66/1.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f54,plain,(
% 7.66/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.66/1.55    inference(cnf_transformation,[],[f8])).
% 7.66/1.55  
% 7.66/1.55  fof(f66,plain,(
% 7.66/1.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.66/1.55    inference(definition_unfolding,[],[f54,f52])).
% 7.66/1.55  
% 7.66/1.55  fof(f2,axiom,(
% 7.66/1.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f31,plain,(
% 7.66/1.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.66/1.55    inference(nnf_transformation,[],[f2])).
% 7.66/1.55  
% 7.66/1.55  fof(f32,plain,(
% 7.66/1.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.66/1.55    inference(flattening,[],[f31])).
% 7.66/1.55  
% 7.66/1.55  fof(f33,plain,(
% 7.66/1.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.66/1.55    inference(rectify,[],[f32])).
% 7.66/1.55  
% 7.66/1.55  fof(f34,plain,(
% 7.66/1.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.66/1.55    introduced(choice_axiom,[])).
% 7.66/1.55  
% 7.66/1.55  fof(f35,plain,(
% 7.66/1.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.66/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 7.66/1.55  
% 7.66/1.55  fof(f44,plain,(
% 7.66/1.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.66/1.55    inference(cnf_transformation,[],[f35])).
% 7.66/1.55  
% 7.66/1.55  fof(f68,plain,(
% 7.66/1.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.66/1.55    inference(equality_resolution,[],[f44])).
% 7.66/1.55  
% 7.66/1.55  fof(f43,plain,(
% 7.66/1.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.66/1.55    inference(cnf_transformation,[],[f35])).
% 7.66/1.55  
% 7.66/1.55  fof(f69,plain,(
% 7.66/1.55    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.66/1.55    inference(equality_resolution,[],[f43])).
% 7.66/1.55  
% 7.66/1.55  fof(f5,axiom,(
% 7.66/1.55    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f18,plain,(
% 7.66/1.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.66/1.55    inference(ennf_transformation,[],[f5])).
% 7.66/1.55  
% 7.66/1.55  fof(f51,plain,(
% 7.66/1.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.66/1.55    inference(cnf_transformation,[],[f18])).
% 7.66/1.55  
% 7.66/1.55  fof(f60,plain,(
% 7.66/1.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.66/1.55    inference(cnf_transformation,[],[f24])).
% 7.66/1.55  
% 7.66/1.55  fof(f3,axiom,(
% 7.66/1.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f16,plain,(
% 7.66/1.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.66/1.55    inference(ennf_transformation,[],[f3])).
% 7.66/1.55  
% 7.66/1.55  fof(f49,plain,(
% 7.66/1.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.66/1.55    inference(cnf_transformation,[],[f16])).
% 7.66/1.55  
% 7.66/1.55  fof(f61,plain,(
% 7.66/1.55    v1_relat_1(sK2)),
% 7.66/1.55    inference(cnf_transformation,[],[f39])).
% 7.66/1.55  
% 7.66/1.55  fof(f7,axiom,(
% 7.66/1.55    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.66/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.55  
% 7.66/1.55  fof(f19,plain,(
% 7.66/1.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.66/1.55    inference(ennf_transformation,[],[f7])).
% 7.66/1.55  
% 7.66/1.55  fof(f20,plain,(
% 7.66/1.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.66/1.55    inference(flattening,[],[f19])).
% 7.66/1.55  
% 7.66/1.55  fof(f53,plain,(
% 7.66/1.55    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.66/1.55    inference(cnf_transformation,[],[f20])).
% 7.66/1.55  
% 7.66/1.55  fof(f64,plain,(
% 7.66/1.55    ~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))),
% 7.66/1.55    inference(cnf_transformation,[],[f39])).
% 7.66/1.55  
% 7.66/1.55  cnf(c_22,negated_conjecture,
% 7.66/1.55      ( v1_relat_1(sK3) ),
% 7.66/1.55      inference(cnf_transformation,[],[f62]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_779,plain,
% 7.66/1.55      ( v1_relat_1(sK3) = iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_17,plain,
% 7.66/1.55      ( ~ v1_relat_1(X0)
% 7.66/1.55      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 7.66/1.55      inference(cnf_transformation,[],[f58]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_782,plain,
% 7.66/1.55      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 7.66/1.55      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_1403,plain,
% 7.66/1.55      ( k2_xboole_0(k1_relat_1(sK3),k2_relat_1(sK3)) = k3_relat_1(sK3) ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_779,c_782]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_1,plain,
% 7.66/1.55      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.66/1.55      inference(cnf_transformation,[],[f41]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_796,plain,
% 7.66/1.55      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.66/1.55      | r1_tarski(X0,X1) = iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_21,negated_conjecture,
% 7.66/1.55      ( r1_tarski(sK2,sK3) ),
% 7.66/1.55      inference(cnf_transformation,[],[f63]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_780,plain,
% 7.66/1.55      ( r1_tarski(sK2,sK3) = iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_19,plain,
% 7.66/1.55      ( ~ r1_tarski(X0,X1)
% 7.66/1.55      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.66/1.55      | ~ v1_relat_1(X0)
% 7.66/1.55      | ~ v1_relat_1(X1) ),
% 7.66/1.55      inference(cnf_transformation,[],[f59]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_16,plain,
% 7.66/1.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.66/1.55      | ~ v1_relat_1(X1)
% 7.66/1.55      | v1_relat_1(X0) ),
% 7.66/1.55      inference(cnf_transformation,[],[f57]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_14,plain,
% 7.66/1.55      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.66/1.55      inference(cnf_transformation,[],[f56]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_236,plain,
% 7.66/1.55      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.66/1.55      | ~ r1_tarski(X0,X1)
% 7.66/1.55      | ~ v1_relat_1(X1) ),
% 7.66/1.55      inference(global_propositional_subsumption,
% 7.66/1.55                [status(thm)],
% 7.66/1.55                [c_19,c_16,c_14]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_237,plain,
% 7.66/1.55      ( ~ r1_tarski(X0,X1)
% 7.66/1.55      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.66/1.55      | ~ v1_relat_1(X1) ),
% 7.66/1.55      inference(renaming,[status(thm)],[c_236]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_776,plain,
% 7.66/1.55      ( r1_tarski(X0,X1) != iProver_top
% 7.66/1.55      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 7.66/1.55      | v1_relat_1(X1) != iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_10,plain,
% 7.66/1.55      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.66/1.55      inference(cnf_transformation,[],[f65]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_787,plain,
% 7.66/1.55      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.66/1.55      | r1_tarski(X0,X1) != iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_13,plain,
% 7.66/1.55      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 7.66/1.55      inference(cnf_transformation,[],[f66]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_824,plain,
% 7.66/1.55      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 7.66/1.55      | r1_tarski(X0,X1) != iProver_top ),
% 7.66/1.55      inference(demodulation,[status(thm)],[c_787,c_13]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_2202,plain,
% 7.66/1.55      ( k1_setfam_1(k2_tarski(k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(X0)
% 7.66/1.55      | r1_tarski(X0,X1) != iProver_top
% 7.66/1.55      | v1_relat_1(X1) != iProver_top ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_776,c_824]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_12279,plain,
% 7.66/1.55      ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),k1_relat_1(sK3))) = k1_relat_1(sK2)
% 7.66/1.55      | v1_relat_1(sK3) != iProver_top ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_780,c_2202]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_25,plain,
% 7.66/1.55      ( v1_relat_1(sK3) = iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_13373,plain,
% 7.66/1.55      ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),k1_relat_1(sK3))) = k1_relat_1(sK2) ),
% 7.66/1.55      inference(global_propositional_subsumption,
% 7.66/1.55                [status(thm)],
% 7.66/1.55                [c_12279,c_25]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_7,plain,
% 7.66/1.55      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.66/1.55      inference(cnf_transformation,[],[f68]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_790,plain,
% 7.66/1.55      ( r2_hidden(X0,X1) != iProver_top
% 7.66/1.55      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_2371,plain,
% 7.66/1.55      ( r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top
% 7.66/1.55      | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_13,c_790]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_13380,plain,
% 7.66/1.55      ( r2_hidden(X0,k4_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3))) != iProver_top
% 7.66/1.55      | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_13373,c_2371]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_8,plain,
% 7.66/1.55      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.66/1.55      inference(cnf_transformation,[],[f69]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_789,plain,
% 7.66/1.55      ( r2_hidden(X0,X1) = iProver_top
% 7.66/1.55      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_14925,plain,
% 7.66/1.55      ( r2_hidden(X0,k4_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3))) != iProver_top ),
% 7.66/1.55      inference(forward_subsumption_resolution,
% 7.66/1.55                [status(thm)],
% 7.66/1.55                [c_13380,c_789]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_14929,plain,
% 7.66/1.55      ( r1_tarski(k4_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)),X0) = iProver_top ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_796,c_14925]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_11,plain,
% 7.66/1.55      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.66/1.55      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.66/1.55      inference(cnf_transformation,[],[f51]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_786,plain,
% 7.66/1.55      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 7.66/1.55      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_22264,plain,
% 7.66/1.55      ( r1_tarski(k1_relat_1(sK2),k2_xboole_0(k1_relat_1(sK3),X0)) = iProver_top ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_14929,c_786]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_25593,plain,
% 7.66/1.55      ( r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) = iProver_top ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_1403,c_22264]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_18,plain,
% 7.66/1.55      ( ~ r1_tarski(X0,X1)
% 7.66/1.55      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.66/1.55      | ~ v1_relat_1(X0)
% 7.66/1.55      | ~ v1_relat_1(X1) ),
% 7.66/1.55      inference(cnf_transformation,[],[f60]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_243,plain,
% 7.66/1.55      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.66/1.55      | ~ r1_tarski(X0,X1)
% 7.66/1.55      | ~ v1_relat_1(X1) ),
% 7.66/1.55      inference(global_propositional_subsumption,
% 7.66/1.55                [status(thm)],
% 7.66/1.55                [c_18,c_16,c_14]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_244,plain,
% 7.66/1.55      ( ~ r1_tarski(X0,X1)
% 7.66/1.55      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.66/1.55      | ~ v1_relat_1(X1) ),
% 7.66/1.55      inference(renaming,[status(thm)],[c_243]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_775,plain,
% 7.66/1.55      ( r1_tarski(X0,X1) != iProver_top
% 7.66/1.55      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 7.66/1.55      | v1_relat_1(X1) != iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_244]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_9,plain,
% 7.66/1.55      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 7.66/1.55      inference(cnf_transformation,[],[f49]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_788,plain,
% 7.66/1.55      ( r1_tarski(X0,X1) != iProver_top
% 7.66/1.55      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_1783,plain,
% 7.66/1.55      ( r1_tarski(X0,k3_relat_1(sK3)) = iProver_top
% 7.66/1.55      | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_1403,c_788]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_1999,plain,
% 7.66/1.55      ( r1_tarski(X0,sK3) != iProver_top
% 7.66/1.55      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK3)) = iProver_top
% 7.66/1.55      | v1_relat_1(sK3) != iProver_top ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_775,c_1783]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_2597,plain,
% 7.66/1.55      ( r1_tarski(k2_relat_1(X0),k3_relat_1(sK3)) = iProver_top
% 7.66/1.55      | r1_tarski(X0,sK3) != iProver_top ),
% 7.66/1.55      inference(global_propositional_subsumption,
% 7.66/1.55                [status(thm)],
% 7.66/1.55                [c_1999,c_25]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_2598,plain,
% 7.66/1.55      ( r1_tarski(X0,sK3) != iProver_top
% 7.66/1.55      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK3)) = iProver_top ),
% 7.66/1.55      inference(renaming,[status(thm)],[c_2597]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_23,negated_conjecture,
% 7.66/1.55      ( v1_relat_1(sK2) ),
% 7.66/1.55      inference(cnf_transformation,[],[f61]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_778,plain,
% 7.66/1.55      ( v1_relat_1(sK2) = iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_1404,plain,
% 7.66/1.55      ( k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) = k3_relat_1(sK2) ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_778,c_782]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_12,plain,
% 7.66/1.55      ( ~ r1_tarski(X0,X1)
% 7.66/1.55      | ~ r1_tarski(X2,X1)
% 7.66/1.55      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 7.66/1.55      inference(cnf_transformation,[],[f53]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_785,plain,
% 7.66/1.55      ( r1_tarski(X0,X1) != iProver_top
% 7.66/1.55      | r1_tarski(X2,X1) != iProver_top
% 7.66/1.55      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_5218,plain,
% 7.66/1.55      ( r1_tarski(k3_relat_1(sK2),X0) = iProver_top
% 7.66/1.55      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 7.66/1.55      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_1404,c_785]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_6586,plain,
% 7.66/1.55      ( r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) = iProver_top
% 7.66/1.55      | r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) != iProver_top
% 7.66/1.55      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.66/1.55      inference(superposition,[status(thm)],[c_2598,c_5218]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_20,negated_conjecture,
% 7.66/1.55      ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) ),
% 7.66/1.55      inference(cnf_transformation,[],[f64]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_27,plain,
% 7.66/1.55      ( r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) != iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(c_26,plain,
% 7.66/1.55      ( r1_tarski(sK2,sK3) = iProver_top ),
% 7.66/1.55      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.66/1.55  
% 7.66/1.55  cnf(contradiction,plain,
% 7.66/1.55      ( $false ),
% 7.66/1.55      inference(minisat,[status(thm)],[c_25593,c_6586,c_27,c_26]) ).
% 7.66/1.55  
% 7.66/1.55  
% 7.66/1.55  % SZS output end CNFRefutation for theBenchmark.p
% 7.66/1.55  
% 7.66/1.55  ------                               Statistics
% 7.66/1.55  
% 7.66/1.55  ------ Selected
% 7.66/1.55  
% 7.66/1.55  total_time:                             0.809
% 7.66/1.55  
%------------------------------------------------------------------------------
