%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0889+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:21 EST 2020

% Result     : Theorem 35.56s
% Output     : CNFRefutation 35.56s
% Verified   : 
% Statistics : Number of formulae       :  156 (1781 expanded)
%              Number of clauses        :   93 ( 587 expanded)
%              Number of leaves         :   16 ( 404 expanded)
%              Depth                    :   28
%              Number of atoms          :  443 (5632 expanded)
%              Number of equality atoms :  284 (3151 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
            & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
            & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & ( r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        | r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        | r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & ( r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          | r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          | r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) )
   => ( k1_xboole_0 != sK1
      & ( r1_tarski(sK1,k3_zfmisc_1(sK3,sK1,sK2))
        | r1_tarski(sK1,k3_zfmisc_1(sK2,sK3,sK1))
        | r1_tarski(sK1,k3_zfmisc_1(sK1,sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    & ( r1_tarski(sK1,k3_zfmisc_1(sK3,sK1,sK2))
      | r1_tarski(sK1,k3_zfmisc_1(sK2,sK3,sK1))
      | r1_tarski(sK1,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f32])).

fof(f53,plain,
    ( r1_tarski(sK1,k3_zfmisc_1(sK3,sK1,sK2))
    | r1_tarski(sK1,k3_zfmisc_1(sK2,sK3,sK1))
    | r1_tarski(sK1,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2))
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK1))
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f53,f34,f34,f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f27])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f34])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f44,f34])).

fof(f65,plain,(
    ! [X2,X1] : k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2) = k1_xboole_0 ),
    inference(equality_resolution,[],[f59])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK0(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f40,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK0(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f46,f34])).

fof(f63,plain,(
    ! [X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f57])).

fof(f9,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f45,f34])).

fof(f64,plain,(
    ! [X2,X0] : k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2) = k1_xboole_0 ),
    inference(equality_resolution,[],[f58])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK1))
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2))
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_939,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK1)) = iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2)) = iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_949,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1480,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2)) = iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_939,c_949])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1237,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2))
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[status(thm)],[c_2,c_19])).

cnf(c_1238,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2)) = iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1237])).

cnf(c_1538,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2)) = iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1480,c_18,c_1238])).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_945,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_944,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_940,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1733,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_944,c_940])).

cnf(c_1739,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(sK0(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_945,c_1733])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k3_mcart_1(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_941,plain,
    ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3126,plain,
    ( k3_mcart_1(k5_mcart_1(X0,X1,X2,sK0(X3)),k6_mcart_1(X0,X1,X2,sK0(X3)),k7_mcart_1(X0,X1,X2,sK0(X3))) = sK0(X3)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | r1_tarski(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_941])).

cnf(c_39022,plain,
    ( k3_mcart_1(k5_mcart_1(sK3,sK1,sK2,sK0(sK1)),k6_mcart_1(sK3,sK1,sK2,sK0(sK1)),k7_mcart_1(sK3,sK1,sK2,sK0(sK1))) = sK0(sK1)
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_3126])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_39,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_40,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1083,plain,
    ( r2_hidden(sK0(sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1084,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(sK0(sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1083])).

cnf(c_556,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1119,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_1120,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_1195,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2))
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1196,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1195])).

cnf(c_1135,plain,
    ( ~ r2_hidden(sK0(sK1),sK1)
    | m1_subset_1(sK0(sK1),X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1256,plain,
    ( ~ r2_hidden(sK0(sK1),sK1)
    | m1_subset_1(sK0(sK1),k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2))) ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_1257,plain,
    ( r2_hidden(sK0(sK1),sK1) != iProver_top
    | m1_subset_1(sK0(sK1),k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1292,plain,
    ( m1_subset_1(k6_mcart_1(sK3,sK1,sK2,sK0(sK1)),sK1)
    | ~ m1_subset_1(sK0(sK1),k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1296,plain,
    ( m1_subset_1(k6_mcart_1(sK3,sK1,sK2,sK0(sK1)),sK1) = iProver_top
    | m1_subset_1(sK0(sK1),k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1292])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_222,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | X2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_223,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_1947,plain,
    ( r2_hidden(k6_mcart_1(sK3,sK1,sK2,sK0(sK1)),sK1)
    | ~ m1_subset_1(k6_mcart_1(sK3,sK1,sK2,sK0(sK1)),sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_1948,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(k6_mcart_1(sK3,sK1,sK2,sK0(sK1)),sK1) = iProver_top
    | m1_subset_1(k6_mcart_1(sK3,sK1,sK2,sK0(sK1)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1947])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_mcart_1(X2,X0,X3) != sK0(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1590,plain,
    ( ~ r2_hidden(X0,sK1)
    | k3_mcart_1(X1,X0,X2) != sK0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6967,plain,
    ( ~ r2_hidden(k6_mcart_1(sK3,sK1,sK2,sK0(sK1)),sK1)
    | k3_mcart_1(k5_mcart_1(sK3,sK1,sK2,sK0(sK1)),k6_mcart_1(sK3,sK1,sK2,sK0(sK1)),k7_mcart_1(sK3,sK1,sK2,sK0(sK1))) != sK0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_6968,plain,
    ( k3_mcart_1(k5_mcart_1(sK3,sK1,sK2,sK0(sK1)),k6_mcart_1(sK3,sK1,sK2,sK0(sK1)),k7_mcart_1(sK3,sK1,sK2,sK0(sK1))) != sK0(sK1)
    | k1_xboole_0 = sK1
    | r2_hidden(k6_mcart_1(sK3,sK1,sK2,sK0(sK1)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6967])).

cnf(c_41215,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39022,c_18,c_39,c_40,c_1084,c_1120,c_1196,c_1238,c_1257,c_1296,c_1948,c_6968])).

cnf(c_41216,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_41215])).

cnf(c_41222,plain,
    ( k3_mcart_1(k5_mcart_1(sK1,sK2,sK3,sK0(sK1)),k6_mcart_1(sK1,sK2,sK3,sK0(sK1)),k7_mcart_1(sK1,sK2,sK3,sK0(sK1))) = sK0(sK1)
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_41216,c_3126])).

cnf(c_41223,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k3_mcart_1(k5_mcart_1(sK1,sK2,sK3,sK0(sK1)),k6_mcart_1(sK1,sK2,sK3,sK0(sK1)),k7_mcart_1(sK1,sK2,sK3,sK0(sK1))) = sK0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41222,c_18,c_39,c_40,c_1120])).

cnf(c_41224,plain,
    ( k3_mcart_1(k5_mcart_1(sK1,sK2,sK3,sK0(sK1)),k6_mcart_1(sK1,sK2,sK3,sK0(sK1)),k7_mcart_1(sK1,sK2,sK3,sK0(sK1))) = sK0(sK1)
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_41223])).

cnf(c_947,plain,
    ( k3_mcart_1(X0,X1,X2) != sK0(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_41228,plain,
    ( sK0(X0) != sK0(sK1)
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK0(sK1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_41224,c_947])).

cnf(c_41783,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK0(sK1)),sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_41228])).

cnf(c_1523,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1524,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1523])).

cnf(c_2507,plain,
    ( ~ r2_hidden(sK0(sK1),sK1)
    | m1_subset_1(sK0(sK1),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_2508,plain,
    ( r2_hidden(sK0(sK1),sK1) != iProver_top
    | m1_subset_1(sK0(sK1),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2507])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3277,plain,
    ( m1_subset_1(k5_mcart_1(sK1,sK2,sK3,sK0(sK1)),sK1)
    | ~ m1_subset_1(sK0(sK1),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3278,plain,
    ( m1_subset_1(k5_mcart_1(sK1,sK2,sK3,sK0(sK1)),sK1) = iProver_top
    | m1_subset_1(sK0(sK1),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3277])).

cnf(c_19772,plain,
    ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK0(sK1)),sK1)
    | ~ m1_subset_1(k5_mcart_1(sK1,sK2,sK3,sK0(sK1)),sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_19773,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK0(sK1)),sK1) = iProver_top
    | m1_subset_1(k5_mcart_1(sK1,sK2,sK3,sK0(sK1)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19772])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_mcart_1(X0,X2,X3) != sK0(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_946,plain,
    ( k3_mcart_1(X0,X1,X2) != sK0(X3)
    | k1_xboole_0 = X3
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_41229,plain,
    ( sK0(X0) != sK0(sK1)
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK0(sK1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_41224,c_946])).

cnf(c_41791,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK0(sK1)),sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_41229])).

cnf(c_41922,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_41783,c_18,c_39,c_40,c_1084,c_1120,c_1524,c_2508,c_3278,c_19773,c_41216,c_41791])).

cnf(c_41929,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK3,sK1),k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_41922,c_1538])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_41934,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_41929,c_8])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1788,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1789,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_41940,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_41934,c_18,c_1789])).

cnf(c_41941,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_41940])).

cnf(c_41946,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_41922,c_41941])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1169,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_9])).

cnf(c_1315,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | k2_zfmisc_1(k1_xboole_0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(superposition,[status(thm)],[c_9,c_11])).

cnf(c_1322,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1315,c_1169])).

cnf(c_1323,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1322])).

cnf(c_2929,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(equality_factoring,[status(thm)],[c_1323])).

cnf(c_2933,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(equality_resolution_simp,[status(thm)],[c_2929])).

cnf(c_37148,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(equality_factoring,[status(thm)],[c_2933])).

cnf(c_37151,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_37148])).

cnf(c_41950,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_41946,c_1169,c_37151])).

cnf(c_42104,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_41950,c_18,c_1789])).

cnf(c_42111,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0),sK1)) = iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_42104,c_939])).

cnf(c_42115,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_42111,c_8,c_1169,c_37151])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42115,c_1789,c_18])).


%------------------------------------------------------------------------------
