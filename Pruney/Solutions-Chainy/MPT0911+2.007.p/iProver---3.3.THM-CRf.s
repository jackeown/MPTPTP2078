%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:01 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 715 expanded)
%              Number of clauses        :   87 ( 205 expanded)
%              Number of leaves         :   19 ( 162 expanded)
%              Depth                    :   20
%              Number of atoms          :  526 (3929 expanded)
%              Number of equality atoms :  346 (2528 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f29,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f29])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k7_mcart_1(sK7,sK8,sK9,sK11) != sK10
      & k1_xboole_0 != sK9
      & k1_xboole_0 != sK8
      & k1_xboole_0 != sK7
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK10 = X7
                  | k3_mcart_1(X5,X6,X7) != sK11
                  | ~ m1_subset_1(X7,sK9) )
              | ~ m1_subset_1(X6,sK8) )
          | ~ m1_subset_1(X5,sK7) )
      & m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k7_mcart_1(sK7,sK8,sK9,sK11) != sK10
    & k1_xboole_0 != sK9
    & k1_xboole_0 != sK8
    & k1_xboole_0 != sK7
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK10 = X7
                | k3_mcart_1(X5,X6,X7) != sK11
                | ~ m1_subset_1(X7,sK9) )
            | ~ m1_subset_1(X6,sK8) )
        | ~ m1_subset_1(X5,sK7) )
    & m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f30,f48])).

fof(f85,plain,(
    m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f102,plain,(
    m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) ),
    inference(definition_unfolding,[],[f85,f71])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f46])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f78,f71])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f79,f71])).

fof(f112,plain,(
    ! [X2,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2) ),
    inference(equality_resolution,[],[f96])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f35])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X6,X7,X5] :
      ( sK10 = X7
      | k3_mcart_1(X5,X6,X7) != sK11
      | ~ m1_subset_1(X7,sK9)
      | ~ m1_subset_1(X6,sK8)
      | ~ m1_subset_1(X5,sK7) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f101,plain,(
    ! [X6,X7,X5] :
      ( sK10 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK11
      | ~ m1_subset_1(X7,sK9)
      | ~ m1_subset_1(X6,sK8)
      | ~ m1_subset_1(X5,sK7) ) ),
    inference(definition_unfolding,[],[f86,f70])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f73,f71])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f83,f71])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f72,f71])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f82,f71])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f84,f71])).

fof(f90,plain,(
    k7_mcart_1(sK7,sK8,sK9,sK11) != sK10 ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f74,f71])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_978,plain,
    ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_983,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X0,k2_zfmisc_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6319,plain,
    ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_978,c_983])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_29,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_52,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_28,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_53,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_517,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1272,plain,
    ( sK9 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_1273,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1272])).

cnf(c_14,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1254,plain,
    ( k2_zfmisc_1(sK7,X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1500,plain,
    ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_6985,plain,
    ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6319,c_36,c_35,c_34,c_52,c_53,c_1273,c_1500])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_989,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2849,plain,
    ( r2_hidden(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_989])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_984,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2863,plain,
    ( r2_hidden(k1_mcart_1(sK11),k2_zfmisc_1(sK7,sK8)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_984])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_179,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_1])).

cnf(c_180,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_977,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_3381,plain,
    ( m1_subset_1(k1_mcart_1(sK11),k2_zfmisc_1(sK7,sK8)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2863,c_977])).

cnf(c_6322,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3381,c_983])).

cnf(c_1274,plain,
    ( sK8 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_1275,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_1276,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_1277,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_7335,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6322,c_36,c_35,c_52,c_53,c_1275,c_1277])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_990,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3926,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) != iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_990])).

cnf(c_7341,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
    | v1_xboole_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_7335,c_3926])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1000,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1002,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2207,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1000,c_1002])).

cnf(c_8667,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
    | sK11 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7341,c_2207])).

cnf(c_1269,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,X0),X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1518,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_2232,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1518])).

cnf(c_8663,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
    | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7335,c_2207])).

cnf(c_8697,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8667,c_36,c_35,c_34,c_2232,c_8663])).

cnf(c_37,negated_conjecture,
    ( ~ m1_subset_1(X0,sK9)
    | ~ m1_subset_1(X1,sK8)
    | ~ m1_subset_1(X2,sK7)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK11
    | sK10 = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_979,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK11
    | sK10 = X2
    | m1_subset_1(X2,sK9) != iProver_top
    | m1_subset_1(X1,sK8) != iProver_top
    | m1_subset_1(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_8700,plain,
    ( k4_tarski(k1_mcart_1(sK11),X0) != sK11
    | sK10 = X0
    | m1_subset_1(X0,sK9) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK11)),sK7) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK11)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8697,c_979])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_987,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6529,plain,
    ( m1_subset_1(k6_mcart_1(sK7,sK8,sK9,sK11),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_987])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_981,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3776,plain,
    ( k6_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(k1_mcart_1(sK11))
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_978,c_981])).

cnf(c_4557,plain,
    ( k6_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(k1_mcart_1(sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3776,c_36,c_35,c_34,c_52,c_53,c_1273,c_1275,c_1277])).

cnf(c_6568,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK11)),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6529,c_4557])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_988,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7504,plain,
    ( m1_subset_1(k5_mcart_1(sK7,sK8,sK9,sK11),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_988])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_980,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2168,plain,
    ( k5_mcart_1(sK7,sK8,sK9,sK11) = k1_mcart_1(k1_mcart_1(sK11))
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_978,c_980])).

cnf(c_3047,plain,
    ( k5_mcart_1(sK7,sK8,sK9,sK11) = k1_mcart_1(k1_mcart_1(sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2168,c_36,c_35,c_34,c_52,c_53,c_1273,c_1275,c_1277])).

cnf(c_7553,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK11)),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7504,c_3047])).

cnf(c_9526,plain,
    ( k4_tarski(k1_mcart_1(sK11),X0) != sK11
    | sK10 = X0
    | m1_subset_1(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8700,c_6568,c_7553])).

cnf(c_9535,plain,
    ( k2_mcart_1(sK11) = sK10
    | m1_subset_1(k2_mcart_1(sK11),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6985,c_9526])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_982,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5102,plain,
    ( k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11)
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_978,c_982])).

cnf(c_1339,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,X1),X2))
    | k7_mcart_1(sK7,X1,X2,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1627,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,X1),sK9))
    | k7_mcart_1(sK7,X1,sK9,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_2802,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))
    | k7_mcart_1(sK7,sK8,sK9,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1627])).

cnf(c_4298,plain,
    ( ~ m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))
    | k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11)
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_2802])).

cnf(c_5656,plain,
    ( k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5102,c_38,c_36,c_35,c_34,c_4298])).

cnf(c_33,negated_conjecture,
    ( k7_mcart_1(sK7,sK8,sK9,sK11) != sK10 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5660,plain,
    ( k2_mcart_1(sK11) != sK10 ),
    inference(demodulation,[status(thm)],[c_5656,c_33])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_986,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5155,plain,
    ( m1_subset_1(k7_mcart_1(sK7,sK8,sK9,sK11),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_986])).

cnf(c_5659,plain,
    ( m1_subset_1(k2_mcart_1(sK11),sK9) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5656,c_5155])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9535,c_5660,c_5659])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.36/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/1.00  
% 3.36/1.00  ------  iProver source info
% 3.36/1.00  
% 3.36/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.36/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/1.00  git: non_committed_changes: false
% 3.36/1.00  git: last_make_outside_of_git: false
% 3.36/1.00  
% 3.36/1.00  ------ 
% 3.36/1.00  
% 3.36/1.00  ------ Input Options
% 3.36/1.00  
% 3.36/1.00  --out_options                           all
% 3.36/1.00  --tptp_safe_out                         true
% 3.36/1.00  --problem_path                          ""
% 3.36/1.00  --include_path                          ""
% 3.36/1.00  --clausifier                            res/vclausify_rel
% 3.36/1.00  --clausifier_options                    --mode clausify
% 3.36/1.00  --stdin                                 false
% 3.36/1.00  --stats_out                             all
% 3.36/1.00  
% 3.36/1.00  ------ General Options
% 3.36/1.00  
% 3.36/1.00  --fof                                   false
% 3.36/1.00  --time_out_real                         305.
% 3.36/1.00  --time_out_virtual                      -1.
% 3.36/1.00  --symbol_type_check                     false
% 3.36/1.00  --clausify_out                          false
% 3.36/1.00  --sig_cnt_out                           false
% 3.36/1.00  --trig_cnt_out                          false
% 3.36/1.00  --trig_cnt_out_tolerance                1.
% 3.36/1.00  --trig_cnt_out_sk_spl                   false
% 3.36/1.00  --abstr_cl_out                          false
% 3.36/1.00  
% 3.36/1.00  ------ Global Options
% 3.36/1.00  
% 3.36/1.00  --schedule                              default
% 3.36/1.00  --add_important_lit                     false
% 3.36/1.00  --prop_solver_per_cl                    1000
% 3.36/1.00  --min_unsat_core                        false
% 3.36/1.00  --soft_assumptions                      false
% 3.36/1.00  --soft_lemma_size                       3
% 3.36/1.00  --prop_impl_unit_size                   0
% 3.36/1.00  --prop_impl_unit                        []
% 3.36/1.00  --share_sel_clauses                     true
% 3.36/1.00  --reset_solvers                         false
% 3.36/1.00  --bc_imp_inh                            [conj_cone]
% 3.36/1.00  --conj_cone_tolerance                   3.
% 3.36/1.00  --extra_neg_conj                        none
% 3.36/1.00  --large_theory_mode                     true
% 3.36/1.00  --prolific_symb_bound                   200
% 3.36/1.00  --lt_threshold                          2000
% 3.36/1.00  --clause_weak_htbl                      true
% 3.36/1.00  --gc_record_bc_elim                     false
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing Options
% 3.36/1.00  
% 3.36/1.00  --preprocessing_flag                    true
% 3.36/1.00  --time_out_prep_mult                    0.1
% 3.36/1.00  --splitting_mode                        input
% 3.36/1.00  --splitting_grd                         true
% 3.36/1.00  --splitting_cvd                         false
% 3.36/1.00  --splitting_cvd_svl                     false
% 3.36/1.00  --splitting_nvd                         32
% 3.36/1.00  --sub_typing                            true
% 3.36/1.00  --prep_gs_sim                           true
% 3.36/1.00  --prep_unflatten                        true
% 3.36/1.00  --prep_res_sim                          true
% 3.36/1.00  --prep_upred                            true
% 3.36/1.00  --prep_sem_filter                       exhaustive
% 3.36/1.00  --prep_sem_filter_out                   false
% 3.36/1.00  --pred_elim                             true
% 3.36/1.00  --res_sim_input                         true
% 3.36/1.00  --eq_ax_congr_red                       true
% 3.36/1.00  --pure_diseq_elim                       true
% 3.36/1.00  --brand_transform                       false
% 3.36/1.00  --non_eq_to_eq                          false
% 3.36/1.00  --prep_def_merge                        true
% 3.36/1.00  --prep_def_merge_prop_impl              false
% 3.36/1.00  --prep_def_merge_mbd                    true
% 3.36/1.00  --prep_def_merge_tr_red                 false
% 3.36/1.00  --prep_def_merge_tr_cl                  false
% 3.36/1.00  --smt_preprocessing                     true
% 3.36/1.00  --smt_ac_axioms                         fast
% 3.36/1.00  --preprocessed_out                      false
% 3.36/1.00  --preprocessed_stats                    false
% 3.36/1.00  
% 3.36/1.00  ------ Abstraction refinement Options
% 3.36/1.00  
% 3.36/1.00  --abstr_ref                             []
% 3.36/1.00  --abstr_ref_prep                        false
% 3.36/1.00  --abstr_ref_until_sat                   false
% 3.36/1.00  --abstr_ref_sig_restrict                funpre
% 3.36/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/1.00  --abstr_ref_under                       []
% 3.36/1.00  
% 3.36/1.00  ------ SAT Options
% 3.36/1.00  
% 3.36/1.00  --sat_mode                              false
% 3.36/1.00  --sat_fm_restart_options                ""
% 3.36/1.00  --sat_gr_def                            false
% 3.36/1.00  --sat_epr_types                         true
% 3.36/1.00  --sat_non_cyclic_types                  false
% 3.36/1.00  --sat_finite_models                     false
% 3.36/1.00  --sat_fm_lemmas                         false
% 3.36/1.00  --sat_fm_prep                           false
% 3.36/1.00  --sat_fm_uc_incr                        true
% 3.36/1.00  --sat_out_model                         small
% 3.36/1.00  --sat_out_clauses                       false
% 3.36/1.00  
% 3.36/1.00  ------ QBF Options
% 3.36/1.00  
% 3.36/1.00  --qbf_mode                              false
% 3.36/1.00  --qbf_elim_univ                         false
% 3.36/1.00  --qbf_dom_inst                          none
% 3.36/1.00  --qbf_dom_pre_inst                      false
% 3.36/1.00  --qbf_sk_in                             false
% 3.36/1.00  --qbf_pred_elim                         true
% 3.36/1.00  --qbf_split                             512
% 3.36/1.00  
% 3.36/1.00  ------ BMC1 Options
% 3.36/1.00  
% 3.36/1.00  --bmc1_incremental                      false
% 3.36/1.00  --bmc1_axioms                           reachable_all
% 3.36/1.00  --bmc1_min_bound                        0
% 3.36/1.00  --bmc1_max_bound                        -1
% 3.36/1.00  --bmc1_max_bound_default                -1
% 3.36/1.00  --bmc1_symbol_reachability              true
% 3.36/1.00  --bmc1_property_lemmas                  false
% 3.36/1.00  --bmc1_k_induction                      false
% 3.36/1.00  --bmc1_non_equiv_states                 false
% 3.36/1.00  --bmc1_deadlock                         false
% 3.36/1.00  --bmc1_ucm                              false
% 3.36/1.00  --bmc1_add_unsat_core                   none
% 3.36/1.00  --bmc1_unsat_core_children              false
% 3.36/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/1.00  --bmc1_out_stat                         full
% 3.36/1.00  --bmc1_ground_init                      false
% 3.36/1.00  --bmc1_pre_inst_next_state              false
% 3.36/1.00  --bmc1_pre_inst_state                   false
% 3.36/1.00  --bmc1_pre_inst_reach_state             false
% 3.36/1.00  --bmc1_out_unsat_core                   false
% 3.36/1.00  --bmc1_aig_witness_out                  false
% 3.36/1.00  --bmc1_verbose                          false
% 3.36/1.00  --bmc1_dump_clauses_tptp                false
% 3.36/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.36/1.00  --bmc1_dump_file                        -
% 3.36/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.36/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.36/1.00  --bmc1_ucm_extend_mode                  1
% 3.36/1.00  --bmc1_ucm_init_mode                    2
% 3.36/1.00  --bmc1_ucm_cone_mode                    none
% 3.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.36/1.00  --bmc1_ucm_relax_model                  4
% 3.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/1.00  --bmc1_ucm_layered_model                none
% 3.36/1.01  --bmc1_ucm_max_lemma_size               10
% 3.36/1.01  
% 3.36/1.01  ------ AIG Options
% 3.36/1.01  
% 3.36/1.01  --aig_mode                              false
% 3.36/1.01  
% 3.36/1.01  ------ Instantiation Options
% 3.36/1.01  
% 3.36/1.01  --instantiation_flag                    true
% 3.36/1.01  --inst_sos_flag                         false
% 3.36/1.01  --inst_sos_phase                        true
% 3.36/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/1.01  --inst_lit_sel_side                     num_symb
% 3.36/1.01  --inst_solver_per_active                1400
% 3.36/1.01  --inst_solver_calls_frac                1.
% 3.36/1.01  --inst_passive_queue_type               priority_queues
% 3.36/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/1.01  --inst_passive_queues_freq              [25;2]
% 3.36/1.01  --inst_dismatching                      true
% 3.36/1.01  --inst_eager_unprocessed_to_passive     true
% 3.36/1.01  --inst_prop_sim_given                   true
% 3.36/1.01  --inst_prop_sim_new                     false
% 3.36/1.01  --inst_subs_new                         false
% 3.36/1.01  --inst_eq_res_simp                      false
% 3.36/1.01  --inst_subs_given                       false
% 3.36/1.01  --inst_orphan_elimination               true
% 3.36/1.01  --inst_learning_loop_flag               true
% 3.36/1.01  --inst_learning_start                   3000
% 3.36/1.01  --inst_learning_factor                  2
% 3.36/1.01  --inst_start_prop_sim_after_learn       3
% 3.36/1.01  --inst_sel_renew                        solver
% 3.36/1.01  --inst_lit_activity_flag                true
% 3.36/1.01  --inst_restr_to_given                   false
% 3.36/1.01  --inst_activity_threshold               500
% 3.36/1.01  --inst_out_proof                        true
% 3.36/1.01  
% 3.36/1.01  ------ Resolution Options
% 3.36/1.01  
% 3.36/1.01  --resolution_flag                       true
% 3.36/1.01  --res_lit_sel                           adaptive
% 3.36/1.01  --res_lit_sel_side                      none
% 3.36/1.01  --res_ordering                          kbo
% 3.36/1.01  --res_to_prop_solver                    active
% 3.36/1.01  --res_prop_simpl_new                    false
% 3.36/1.01  --res_prop_simpl_given                  true
% 3.36/1.01  --res_passive_queue_type                priority_queues
% 3.36/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/1.01  --res_passive_queues_freq               [15;5]
% 3.36/1.01  --res_forward_subs                      full
% 3.36/1.01  --res_backward_subs                     full
% 3.36/1.01  --res_forward_subs_resolution           true
% 3.36/1.01  --res_backward_subs_resolution          true
% 3.36/1.01  --res_orphan_elimination                true
% 3.36/1.01  --res_time_limit                        2.
% 3.36/1.01  --res_out_proof                         true
% 3.36/1.01  
% 3.36/1.01  ------ Superposition Options
% 3.36/1.01  
% 3.36/1.01  --superposition_flag                    true
% 3.36/1.01  --sup_passive_queue_type                priority_queues
% 3.36/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.36/1.01  --demod_completeness_check              fast
% 3.36/1.01  --demod_use_ground                      true
% 3.36/1.01  --sup_to_prop_solver                    passive
% 3.36/1.01  --sup_prop_simpl_new                    true
% 3.36/1.01  --sup_prop_simpl_given                  true
% 3.36/1.01  --sup_fun_splitting                     false
% 3.36/1.01  --sup_smt_interval                      50000
% 3.36/1.01  
% 3.36/1.01  ------ Superposition Simplification Setup
% 3.36/1.01  
% 3.36/1.01  --sup_indices_passive                   []
% 3.36/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.01  --sup_full_bw                           [BwDemod]
% 3.36/1.01  --sup_immed_triv                        [TrivRules]
% 3.36/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.01  --sup_immed_bw_main                     []
% 3.36/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.01  
% 3.36/1.01  ------ Combination Options
% 3.36/1.01  
% 3.36/1.01  --comb_res_mult                         3
% 3.36/1.01  --comb_sup_mult                         2
% 3.36/1.01  --comb_inst_mult                        10
% 3.36/1.01  
% 3.36/1.01  ------ Debug Options
% 3.36/1.01  
% 3.36/1.01  --dbg_backtrace                         false
% 3.36/1.01  --dbg_dump_prop_clauses                 false
% 3.36/1.01  --dbg_dump_prop_clauses_file            -
% 3.36/1.01  --dbg_out_stat                          false
% 3.36/1.01  ------ Parsing...
% 3.36/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/1.01  
% 3.36/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.36/1.01  
% 3.36/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/1.01  
% 3.36/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/1.01  ------ Proving...
% 3.36/1.01  ------ Problem Properties 
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  clauses                                 38
% 3.36/1.01  conjectures                             6
% 3.36/1.01  EPR                                     9
% 3.36/1.01  Horn                                    26
% 3.36/1.01  unary                                   11
% 3.36/1.01  binary                                  12
% 3.36/1.01  lits                                    92
% 3.36/1.01  lits eq                                 41
% 3.36/1.01  fd_pure                                 0
% 3.36/1.01  fd_pseudo                               0
% 3.36/1.01  fd_cond                                 7
% 3.36/1.01  fd_pseudo_cond                          4
% 3.36/1.01  AC symbols                              0
% 3.36/1.01  
% 3.36/1.01  ------ Schedule dynamic 5 is on 
% 3.36/1.01  
% 3.36/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  ------ 
% 3.36/1.01  Current options:
% 3.36/1.01  ------ 
% 3.36/1.01  
% 3.36/1.01  ------ Input Options
% 3.36/1.01  
% 3.36/1.01  --out_options                           all
% 3.36/1.01  --tptp_safe_out                         true
% 3.36/1.01  --problem_path                          ""
% 3.36/1.01  --include_path                          ""
% 3.36/1.01  --clausifier                            res/vclausify_rel
% 3.36/1.01  --clausifier_options                    --mode clausify
% 3.36/1.01  --stdin                                 false
% 3.36/1.01  --stats_out                             all
% 3.36/1.01  
% 3.36/1.01  ------ General Options
% 3.36/1.01  
% 3.36/1.01  --fof                                   false
% 3.36/1.01  --time_out_real                         305.
% 3.36/1.01  --time_out_virtual                      -1.
% 3.36/1.01  --symbol_type_check                     false
% 3.36/1.01  --clausify_out                          false
% 3.36/1.01  --sig_cnt_out                           false
% 3.36/1.01  --trig_cnt_out                          false
% 3.36/1.01  --trig_cnt_out_tolerance                1.
% 3.36/1.01  --trig_cnt_out_sk_spl                   false
% 3.36/1.01  --abstr_cl_out                          false
% 3.36/1.01  
% 3.36/1.01  ------ Global Options
% 3.36/1.01  
% 3.36/1.01  --schedule                              default
% 3.36/1.01  --add_important_lit                     false
% 3.36/1.01  --prop_solver_per_cl                    1000
% 3.36/1.01  --min_unsat_core                        false
% 3.36/1.01  --soft_assumptions                      false
% 3.36/1.01  --soft_lemma_size                       3
% 3.36/1.01  --prop_impl_unit_size                   0
% 3.36/1.01  --prop_impl_unit                        []
% 3.36/1.01  --share_sel_clauses                     true
% 3.36/1.01  --reset_solvers                         false
% 3.36/1.01  --bc_imp_inh                            [conj_cone]
% 3.36/1.01  --conj_cone_tolerance                   3.
% 3.36/1.01  --extra_neg_conj                        none
% 3.36/1.01  --large_theory_mode                     true
% 3.36/1.01  --prolific_symb_bound                   200
% 3.36/1.01  --lt_threshold                          2000
% 3.36/1.01  --clause_weak_htbl                      true
% 3.36/1.01  --gc_record_bc_elim                     false
% 3.36/1.01  
% 3.36/1.01  ------ Preprocessing Options
% 3.36/1.01  
% 3.36/1.01  --preprocessing_flag                    true
% 3.36/1.01  --time_out_prep_mult                    0.1
% 3.36/1.01  --splitting_mode                        input
% 3.36/1.01  --splitting_grd                         true
% 3.36/1.01  --splitting_cvd                         false
% 3.36/1.01  --splitting_cvd_svl                     false
% 3.36/1.01  --splitting_nvd                         32
% 3.36/1.01  --sub_typing                            true
% 3.36/1.01  --prep_gs_sim                           true
% 3.36/1.01  --prep_unflatten                        true
% 3.36/1.01  --prep_res_sim                          true
% 3.36/1.01  --prep_upred                            true
% 3.36/1.01  --prep_sem_filter                       exhaustive
% 3.36/1.01  --prep_sem_filter_out                   false
% 3.36/1.01  --pred_elim                             true
% 3.36/1.01  --res_sim_input                         true
% 3.36/1.01  --eq_ax_congr_red                       true
% 3.36/1.01  --pure_diseq_elim                       true
% 3.36/1.01  --brand_transform                       false
% 3.36/1.01  --non_eq_to_eq                          false
% 3.36/1.01  --prep_def_merge                        true
% 3.36/1.01  --prep_def_merge_prop_impl              false
% 3.36/1.01  --prep_def_merge_mbd                    true
% 3.36/1.01  --prep_def_merge_tr_red                 false
% 3.36/1.01  --prep_def_merge_tr_cl                  false
% 3.36/1.01  --smt_preprocessing                     true
% 3.36/1.01  --smt_ac_axioms                         fast
% 3.36/1.01  --preprocessed_out                      false
% 3.36/1.01  --preprocessed_stats                    false
% 3.36/1.01  
% 3.36/1.01  ------ Abstraction refinement Options
% 3.36/1.01  
% 3.36/1.01  --abstr_ref                             []
% 3.36/1.01  --abstr_ref_prep                        false
% 3.36/1.01  --abstr_ref_until_sat                   false
% 3.36/1.01  --abstr_ref_sig_restrict                funpre
% 3.36/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/1.01  --abstr_ref_under                       []
% 3.36/1.01  
% 3.36/1.01  ------ SAT Options
% 3.36/1.01  
% 3.36/1.01  --sat_mode                              false
% 3.36/1.01  --sat_fm_restart_options                ""
% 3.36/1.01  --sat_gr_def                            false
% 3.36/1.01  --sat_epr_types                         true
% 3.36/1.01  --sat_non_cyclic_types                  false
% 3.36/1.01  --sat_finite_models                     false
% 3.36/1.01  --sat_fm_lemmas                         false
% 3.36/1.01  --sat_fm_prep                           false
% 3.36/1.01  --sat_fm_uc_incr                        true
% 3.36/1.01  --sat_out_model                         small
% 3.36/1.01  --sat_out_clauses                       false
% 3.36/1.01  
% 3.36/1.01  ------ QBF Options
% 3.36/1.01  
% 3.36/1.01  --qbf_mode                              false
% 3.36/1.01  --qbf_elim_univ                         false
% 3.36/1.01  --qbf_dom_inst                          none
% 3.36/1.01  --qbf_dom_pre_inst                      false
% 3.36/1.01  --qbf_sk_in                             false
% 3.36/1.01  --qbf_pred_elim                         true
% 3.36/1.01  --qbf_split                             512
% 3.36/1.01  
% 3.36/1.01  ------ BMC1 Options
% 3.36/1.01  
% 3.36/1.01  --bmc1_incremental                      false
% 3.36/1.01  --bmc1_axioms                           reachable_all
% 3.36/1.01  --bmc1_min_bound                        0
% 3.36/1.01  --bmc1_max_bound                        -1
% 3.36/1.01  --bmc1_max_bound_default                -1
% 3.36/1.01  --bmc1_symbol_reachability              true
% 3.36/1.01  --bmc1_property_lemmas                  false
% 3.36/1.01  --bmc1_k_induction                      false
% 3.36/1.01  --bmc1_non_equiv_states                 false
% 3.36/1.01  --bmc1_deadlock                         false
% 3.36/1.01  --bmc1_ucm                              false
% 3.36/1.01  --bmc1_add_unsat_core                   none
% 3.36/1.01  --bmc1_unsat_core_children              false
% 3.36/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/1.01  --bmc1_out_stat                         full
% 3.36/1.01  --bmc1_ground_init                      false
% 3.36/1.01  --bmc1_pre_inst_next_state              false
% 3.36/1.01  --bmc1_pre_inst_state                   false
% 3.36/1.01  --bmc1_pre_inst_reach_state             false
% 3.36/1.01  --bmc1_out_unsat_core                   false
% 3.36/1.01  --bmc1_aig_witness_out                  false
% 3.36/1.01  --bmc1_verbose                          false
% 3.36/1.01  --bmc1_dump_clauses_tptp                false
% 3.36/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.36/1.01  --bmc1_dump_file                        -
% 3.36/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.36/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.36/1.01  --bmc1_ucm_extend_mode                  1
% 3.36/1.01  --bmc1_ucm_init_mode                    2
% 3.36/1.01  --bmc1_ucm_cone_mode                    none
% 3.36/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.36/1.01  --bmc1_ucm_relax_model                  4
% 3.36/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.36/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/1.01  --bmc1_ucm_layered_model                none
% 3.36/1.01  --bmc1_ucm_max_lemma_size               10
% 3.36/1.01  
% 3.36/1.01  ------ AIG Options
% 3.36/1.01  
% 3.36/1.01  --aig_mode                              false
% 3.36/1.01  
% 3.36/1.01  ------ Instantiation Options
% 3.36/1.01  
% 3.36/1.01  --instantiation_flag                    true
% 3.36/1.01  --inst_sos_flag                         false
% 3.36/1.01  --inst_sos_phase                        true
% 3.36/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/1.01  --inst_lit_sel_side                     none
% 3.36/1.01  --inst_solver_per_active                1400
% 3.36/1.01  --inst_solver_calls_frac                1.
% 3.36/1.01  --inst_passive_queue_type               priority_queues
% 3.36/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/1.01  --inst_passive_queues_freq              [25;2]
% 3.36/1.01  --inst_dismatching                      true
% 3.36/1.01  --inst_eager_unprocessed_to_passive     true
% 3.36/1.01  --inst_prop_sim_given                   true
% 3.36/1.01  --inst_prop_sim_new                     false
% 3.36/1.01  --inst_subs_new                         false
% 3.36/1.01  --inst_eq_res_simp                      false
% 3.36/1.01  --inst_subs_given                       false
% 3.36/1.01  --inst_orphan_elimination               true
% 3.36/1.01  --inst_learning_loop_flag               true
% 3.36/1.01  --inst_learning_start                   3000
% 3.36/1.01  --inst_learning_factor                  2
% 3.36/1.01  --inst_start_prop_sim_after_learn       3
% 3.36/1.01  --inst_sel_renew                        solver
% 3.36/1.01  --inst_lit_activity_flag                true
% 3.36/1.01  --inst_restr_to_given                   false
% 3.36/1.01  --inst_activity_threshold               500
% 3.36/1.01  --inst_out_proof                        true
% 3.36/1.01  
% 3.36/1.01  ------ Resolution Options
% 3.36/1.01  
% 3.36/1.01  --resolution_flag                       false
% 3.36/1.01  --res_lit_sel                           adaptive
% 3.36/1.01  --res_lit_sel_side                      none
% 3.36/1.01  --res_ordering                          kbo
% 3.36/1.01  --res_to_prop_solver                    active
% 3.36/1.01  --res_prop_simpl_new                    false
% 3.36/1.01  --res_prop_simpl_given                  true
% 3.36/1.01  --res_passive_queue_type                priority_queues
% 3.36/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/1.01  --res_passive_queues_freq               [15;5]
% 3.36/1.01  --res_forward_subs                      full
% 3.36/1.01  --res_backward_subs                     full
% 3.36/1.01  --res_forward_subs_resolution           true
% 3.36/1.01  --res_backward_subs_resolution          true
% 3.36/1.01  --res_orphan_elimination                true
% 3.36/1.01  --res_time_limit                        2.
% 3.36/1.01  --res_out_proof                         true
% 3.36/1.01  
% 3.36/1.01  ------ Superposition Options
% 3.36/1.01  
% 3.36/1.01  --superposition_flag                    true
% 3.36/1.01  --sup_passive_queue_type                priority_queues
% 3.36/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.36/1.01  --demod_completeness_check              fast
% 3.36/1.01  --demod_use_ground                      true
% 3.36/1.01  --sup_to_prop_solver                    passive
% 3.36/1.01  --sup_prop_simpl_new                    true
% 3.36/1.01  --sup_prop_simpl_given                  true
% 3.36/1.01  --sup_fun_splitting                     false
% 3.36/1.01  --sup_smt_interval                      50000
% 3.36/1.01  
% 3.36/1.01  ------ Superposition Simplification Setup
% 3.36/1.01  
% 3.36/1.01  --sup_indices_passive                   []
% 3.36/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.01  --sup_full_bw                           [BwDemod]
% 3.36/1.01  --sup_immed_triv                        [TrivRules]
% 3.36/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.01  --sup_immed_bw_main                     []
% 3.36/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.01  
% 3.36/1.01  ------ Combination Options
% 3.36/1.01  
% 3.36/1.01  --comb_res_mult                         3
% 3.36/1.01  --comb_sup_mult                         2
% 3.36/1.01  --comb_inst_mult                        10
% 3.36/1.01  
% 3.36/1.01  ------ Debug Options
% 3.36/1.01  
% 3.36/1.01  --dbg_backtrace                         false
% 3.36/1.01  --dbg_dump_prop_clauses                 false
% 3.36/1.01  --dbg_dump_prop_clauses_file            -
% 3.36/1.01  --dbg_out_stat                          false
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  ------ Proving...
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  % SZS status Theorem for theBenchmark.p
% 3.36/1.01  
% 3.36/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/1.01  
% 3.36/1.01  fof(f17,conjecture,(
% 3.36/1.01    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f18,negated_conjecture,(
% 3.36/1.01    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.36/1.01    inference(negated_conjecture,[],[f17])).
% 3.36/1.01  
% 3.36/1.01  fof(f29,plain,(
% 3.36/1.01    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.36/1.01    inference(ennf_transformation,[],[f18])).
% 3.36/1.01  
% 3.36/1.01  fof(f30,plain,(
% 3.36/1.01    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.36/1.01    inference(flattening,[],[f29])).
% 3.36/1.01  
% 3.36/1.01  fof(f48,plain,(
% 3.36/1.01    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK7,sK8,sK9,sK11) != sK10 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & ! [X5] : (! [X6] : (! [X7] : (sK10 = X7 | k3_mcart_1(X5,X6,X7) != sK11 | ~m1_subset_1(X7,sK9)) | ~m1_subset_1(X6,sK8)) | ~m1_subset_1(X5,sK7)) & m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9)))),
% 3.36/1.01    introduced(choice_axiom,[])).
% 3.36/1.01  
% 3.36/1.01  fof(f49,plain,(
% 3.36/1.01    k7_mcart_1(sK7,sK8,sK9,sK11) != sK10 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & ! [X5] : (! [X6] : (! [X7] : (sK10 = X7 | k3_mcart_1(X5,X6,X7) != sK11 | ~m1_subset_1(X7,sK9)) | ~m1_subset_1(X6,sK8)) | ~m1_subset_1(X5,sK7)) & m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9))),
% 3.36/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f30,f48])).
% 3.36/1.01  
% 3.36/1.01  fof(f85,plain,(
% 3.36/1.01    m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9))),
% 3.36/1.01    inference(cnf_transformation,[],[f49])).
% 3.36/1.01  
% 3.36/1.01  fof(f9,axiom,(
% 3.36/1.01    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f71,plain,(
% 3.36/1.01    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f9])).
% 3.36/1.01  
% 3.36/1.01  fof(f102,plain,(
% 3.36/1.01    m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))),
% 3.36/1.01    inference(definition_unfolding,[],[f85,f71])).
% 3.36/1.01  
% 3.36/1.01  fof(f14,axiom,(
% 3.36/1.01    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f27,plain,(
% 3.36/1.01    ! [X0,X1] : (! [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.36/1.01    inference(ennf_transformation,[],[f14])).
% 3.36/1.01  
% 3.36/1.01  fof(f77,plain,(
% 3.36/1.01    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/1.01    inference(cnf_transformation,[],[f27])).
% 3.36/1.01  
% 3.36/1.01  fof(f87,plain,(
% 3.36/1.01    k1_xboole_0 != sK7),
% 3.36/1.01    inference(cnf_transformation,[],[f49])).
% 3.36/1.01  
% 3.36/1.01  fof(f88,plain,(
% 3.36/1.01    k1_xboole_0 != sK8),
% 3.36/1.01    inference(cnf_transformation,[],[f49])).
% 3.36/1.01  
% 3.36/1.01  fof(f89,plain,(
% 3.36/1.01    k1_xboole_0 != sK9),
% 3.36/1.01    inference(cnf_transformation,[],[f49])).
% 3.36/1.01  
% 3.36/1.01  fof(f15,axiom,(
% 3.36/1.01    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f46,plain,(
% 3.36/1.01    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.36/1.01    inference(nnf_transformation,[],[f15])).
% 3.36/1.01  
% 3.36/1.01  fof(f47,plain,(
% 3.36/1.01    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.36/1.01    inference(flattening,[],[f46])).
% 3.36/1.01  
% 3.36/1.01  fof(f78,plain,(
% 3.36/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/1.01    inference(cnf_transformation,[],[f47])).
% 3.36/1.01  
% 3.36/1.01  fof(f97,plain,(
% 3.36/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/1.01    inference(definition_unfolding,[],[f78,f71])).
% 3.36/1.01  
% 3.36/1.01  fof(f79,plain,(
% 3.36/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f47])).
% 3.36/1.01  
% 3.36/1.01  fof(f96,plain,(
% 3.36/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.36/1.01    inference(definition_unfolding,[],[f79,f71])).
% 3.36/1.01  
% 3.36/1.01  fof(f112,plain,(
% 3.36/1.01    ( ! [X2,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)) )),
% 3.36/1.01    inference(equality_resolution,[],[f96])).
% 3.36/1.01  
% 3.36/1.01  fof(f5,axiom,(
% 3.36/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f43,plain,(
% 3.36/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.36/1.01    inference(nnf_transformation,[],[f5])).
% 3.36/1.01  
% 3.36/1.01  fof(f44,plain,(
% 3.36/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.36/1.01    inference(flattening,[],[f43])).
% 3.36/1.01  
% 3.36/1.01  fof(f62,plain,(
% 3.36/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f44])).
% 3.36/1.01  
% 3.36/1.01  fof(f7,axiom,(
% 3.36/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f21,plain,(
% 3.36/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.36/1.01    inference(ennf_transformation,[],[f7])).
% 3.36/1.01  
% 3.36/1.01  fof(f22,plain,(
% 3.36/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.36/1.01    inference(flattening,[],[f21])).
% 3.36/1.01  
% 3.36/1.01  fof(f69,plain,(
% 3.36/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f22])).
% 3.36/1.01  
% 3.36/1.01  fof(f13,axiom,(
% 3.36/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f26,plain,(
% 3.36/1.01    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.36/1.01    inference(ennf_transformation,[],[f13])).
% 3.36/1.01  
% 3.36/1.01  fof(f75,plain,(
% 3.36/1.01    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.36/1.01    inference(cnf_transformation,[],[f26])).
% 3.36/1.01  
% 3.36/1.01  fof(f6,axiom,(
% 3.36/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f20,plain,(
% 3.36/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.36/1.01    inference(ennf_transformation,[],[f6])).
% 3.36/1.01  
% 3.36/1.01  fof(f45,plain,(
% 3.36/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.36/1.01    inference(nnf_transformation,[],[f20])).
% 3.36/1.01  
% 3.36/1.01  fof(f66,plain,(
% 3.36/1.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f45])).
% 3.36/1.01  
% 3.36/1.01  fof(f1,axiom,(
% 3.36/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f31,plain,(
% 3.36/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.36/1.01    inference(nnf_transformation,[],[f1])).
% 3.36/1.01  
% 3.36/1.01  fof(f32,plain,(
% 3.36/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.36/1.01    inference(rectify,[],[f31])).
% 3.36/1.01  
% 3.36/1.01  fof(f33,plain,(
% 3.36/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.36/1.01    introduced(choice_axiom,[])).
% 3.36/1.01  
% 3.36/1.01  fof(f34,plain,(
% 3.36/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.36/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 3.36/1.01  
% 3.36/1.01  fof(f50,plain,(
% 3.36/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f34])).
% 3.36/1.01  
% 3.36/1.01  fof(f67,plain,(
% 3.36/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f45])).
% 3.36/1.01  
% 3.36/1.01  fof(f3,axiom,(
% 3.36/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f19,plain,(
% 3.36/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.36/1.01    inference(ennf_transformation,[],[f3])).
% 3.36/1.01  
% 3.36/1.01  fof(f35,plain,(
% 3.36/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.36/1.01    introduced(choice_axiom,[])).
% 3.36/1.01  
% 3.36/1.01  fof(f36,plain,(
% 3.36/1.01    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.36/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f35])).
% 3.36/1.01  
% 3.36/1.01  fof(f53,plain,(
% 3.36/1.01    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.36/1.01    inference(cnf_transformation,[],[f36])).
% 3.36/1.01  
% 3.36/1.01  fof(f86,plain,(
% 3.36/1.01    ( ! [X6,X7,X5] : (sK10 = X7 | k3_mcart_1(X5,X6,X7) != sK11 | ~m1_subset_1(X7,sK9) | ~m1_subset_1(X6,sK8) | ~m1_subset_1(X5,sK7)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f49])).
% 3.36/1.01  
% 3.36/1.01  fof(f8,axiom,(
% 3.36/1.01    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f70,plain,(
% 3.36/1.01    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f8])).
% 3.36/1.01  
% 3.36/1.01  fof(f101,plain,(
% 3.36/1.01    ( ! [X6,X7,X5] : (sK10 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK11 | ~m1_subset_1(X7,sK9) | ~m1_subset_1(X6,sK8) | ~m1_subset_1(X5,sK7)) )),
% 3.36/1.01    inference(definition_unfolding,[],[f86,f70])).
% 3.36/1.01  
% 3.36/1.01  fof(f11,axiom,(
% 3.36/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f24,plain,(
% 3.36/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.36/1.01    inference(ennf_transformation,[],[f11])).
% 3.36/1.01  
% 3.36/1.01  fof(f73,plain,(
% 3.36/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.36/1.01    inference(cnf_transformation,[],[f24])).
% 3.36/1.01  
% 3.36/1.01  fof(f92,plain,(
% 3.36/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.36/1.01    inference(definition_unfolding,[],[f73,f71])).
% 3.36/1.01  
% 3.36/1.01  fof(f16,axiom,(
% 3.36/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f28,plain,(
% 3.36/1.01    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.36/1.01    inference(ennf_transformation,[],[f16])).
% 3.36/1.01  
% 3.36/1.01  fof(f83,plain,(
% 3.36/1.01    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/1.01    inference(cnf_transformation,[],[f28])).
% 3.36/1.01  
% 3.36/1.01  fof(f99,plain,(
% 3.36/1.01    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/1.01    inference(definition_unfolding,[],[f83,f71])).
% 3.36/1.01  
% 3.36/1.01  fof(f10,axiom,(
% 3.36/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f23,plain,(
% 3.36/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.36/1.01    inference(ennf_transformation,[],[f10])).
% 3.36/1.01  
% 3.36/1.01  fof(f72,plain,(
% 3.36/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.36/1.01    inference(cnf_transformation,[],[f23])).
% 3.36/1.01  
% 3.36/1.01  fof(f91,plain,(
% 3.36/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.36/1.01    inference(definition_unfolding,[],[f72,f71])).
% 3.36/1.01  
% 3.36/1.01  fof(f82,plain,(
% 3.36/1.01    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/1.01    inference(cnf_transformation,[],[f28])).
% 3.36/1.01  
% 3.36/1.01  fof(f100,plain,(
% 3.36/1.01    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/1.01    inference(definition_unfolding,[],[f82,f71])).
% 3.36/1.01  
% 3.36/1.01  fof(f84,plain,(
% 3.36/1.01    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/1.01    inference(cnf_transformation,[],[f28])).
% 3.36/1.01  
% 3.36/1.01  fof(f98,plain,(
% 3.36/1.01    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/1.01    inference(definition_unfolding,[],[f84,f71])).
% 3.36/1.01  
% 3.36/1.01  fof(f90,plain,(
% 3.36/1.01    k7_mcart_1(sK7,sK8,sK9,sK11) != sK10),
% 3.36/1.01    inference(cnf_transformation,[],[f49])).
% 3.36/1.01  
% 3.36/1.01  fof(f12,axiom,(
% 3.36/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f25,plain,(
% 3.36/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.36/1.01    inference(ennf_transformation,[],[f12])).
% 3.36/1.01  
% 3.36/1.01  fof(f74,plain,(
% 3.36/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.36/1.01    inference(cnf_transformation,[],[f25])).
% 3.36/1.01  
% 3.36/1.01  fof(f93,plain,(
% 3.36/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.36/1.01    inference(definition_unfolding,[],[f74,f71])).
% 3.36/1.01  
% 3.36/1.01  cnf(c_38,negated_conjecture,
% 3.36/1.01      ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) ),
% 3.36/1.01      inference(cnf_transformation,[],[f102]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_978,plain,
% 3.36/1.01      ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_25,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
% 3.36/1.01      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.36/1.01      | k1_xboole_0 = X1
% 3.36/1.01      | k1_xboole_0 = X2 ),
% 3.36/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_983,plain,
% 3.36/1.01      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.36/1.01      | k1_xboole_0 = X1
% 3.36/1.01      | k1_xboole_0 = X2
% 3.36/1.01      | m1_subset_1(X0,k2_zfmisc_1(X2,X1)) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_6319,plain,
% 3.36/1.01      ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
% 3.36/1.01      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 3.36/1.01      | sK9 = k1_xboole_0 ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_978,c_983]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_36,negated_conjecture,
% 3.36/1.01      ( k1_xboole_0 != sK7 ),
% 3.36/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_35,negated_conjecture,
% 3.36/1.01      ( k1_xboole_0 != sK8 ),
% 3.36/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_34,negated_conjecture,
% 3.36/1.01      ( k1_xboole_0 != sK9 ),
% 3.36/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_29,plain,
% 3.36/1.01      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
% 3.36/1.01      | k1_xboole_0 = X0
% 3.36/1.01      | k1_xboole_0 = X1
% 3.36/1.01      | k1_xboole_0 = X2 ),
% 3.36/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_52,plain,
% 3.36/1.01      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 3.36/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_29]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_28,plain,
% 3.36/1.01      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) = k1_xboole_0 ),
% 3.36/1.01      inference(cnf_transformation,[],[f112]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_53,plain,
% 3.36/1.01      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_28]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_517,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1272,plain,
% 3.36/1.01      ( sK9 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK9 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_517]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1273,plain,
% 3.36/1.01      ( sK9 != k1_xboole_0
% 3.36/1.01      | k1_xboole_0 = sK9
% 3.36/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_1272]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_14,plain,
% 3.36/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.36/1.01      | k1_xboole_0 = X0
% 3.36/1.01      | k1_xboole_0 = X1 ),
% 3.36/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1254,plain,
% 3.36/1.01      ( k2_zfmisc_1(sK7,X0) != k1_xboole_0
% 3.36/1.01      | k1_xboole_0 = X0
% 3.36/1.01      | k1_xboole_0 = sK7 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1500,plain,
% 3.36/1.01      ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
% 3.36/1.01      | k1_xboole_0 = sK8
% 3.36/1.01      | k1_xboole_0 = sK7 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_1254]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_6985,plain,
% 3.36/1.01      ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11 ),
% 3.36/1.01      inference(global_propositional_subsumption,
% 3.36/1.01                [status(thm)],
% 3.36/1.01                [c_6319,c_36,c_35,c_34,c_52,c_53,c_1273,c_1500]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_19,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.36/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_989,plain,
% 3.36/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 3.36/1.01      | r2_hidden(X0,X1) = iProver_top
% 3.36/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_2849,plain,
% 3.36/1.01      ( r2_hidden(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
% 3.36/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_978,c_989]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_24,plain,
% 3.36/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.36/1.01      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.36/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_984,plain,
% 3.36/1.01      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.36/1.01      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_2863,plain,
% 3.36/1.01      ( r2_hidden(k1_mcart_1(sK11),k2_zfmisc_1(sK7,sK8)) = iProver_top
% 3.36/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_2849,c_984]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_17,plain,
% 3.36/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.36/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1,plain,
% 3.36/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.36/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_179,plain,
% 3.36/1.01      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.36/1.01      inference(global_propositional_subsumption,
% 3.36/1.01                [status(thm)],
% 3.36/1.01                [c_17,c_1]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_180,plain,
% 3.36/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.36/1.01      inference(renaming,[status(thm)],[c_179]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_977,plain,
% 3.36/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 3.36/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_180]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_3381,plain,
% 3.36/1.01      ( m1_subset_1(k1_mcart_1(sK11),k2_zfmisc_1(sK7,sK8)) = iProver_top
% 3.36/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_2863,c_977]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_6322,plain,
% 3.36/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
% 3.36/1.01      | sK8 = k1_xboole_0
% 3.36/1.01      | sK7 = k1_xboole_0
% 3.36/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_3381,c_983]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1274,plain,
% 3.36/1.01      ( sK8 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK8 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_517]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1275,plain,
% 3.36/1.01      ( sK8 != k1_xboole_0
% 3.36/1.01      | k1_xboole_0 = sK8
% 3.36/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_1274]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1276,plain,
% 3.36/1.01      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_517]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1277,plain,
% 3.36/1.01      ( sK7 != k1_xboole_0
% 3.36/1.01      | k1_xboole_0 = sK7
% 3.36/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_1276]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_7335,plain,
% 3.36/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
% 3.36/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.36/1.01      inference(global_propositional_subsumption,
% 3.36/1.01                [status(thm)],
% 3.36/1.01                [c_6322,c_36,c_35,c_52,c_53,c_1275,c_1277]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_16,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.36/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_990,plain,
% 3.36/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 3.36/1.01      | v1_xboole_0(X1) != iProver_top
% 3.36/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_3926,plain,
% 3.36/1.01      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) != iProver_top
% 3.36/1.01      | v1_xboole_0(sK11) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_978,c_990]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_7341,plain,
% 3.36/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
% 3.36/1.01      | v1_xboole_0(sK11) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_7335,c_3926]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_3,plain,
% 3.36/1.01      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.36/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1000,plain,
% 3.36/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1002,plain,
% 3.36/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.36/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_2207,plain,
% 3.36/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_1000,c_1002]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_8667,plain,
% 3.36/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
% 3.36/1.01      | sK11 = k1_xboole_0 ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_7341,c_2207]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1269,plain,
% 3.36/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK7,X0),X1) != k1_xboole_0
% 3.36/1.01      | k1_xboole_0 = X0
% 3.36/1.01      | k1_xboole_0 = X1
% 3.36/1.01      | k1_xboole_0 = sK7 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_29]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1518,plain,
% 3.36/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) != k1_xboole_0
% 3.36/1.01      | k1_xboole_0 = X0
% 3.36/1.01      | k1_xboole_0 = sK8
% 3.36/1.01      | k1_xboole_0 = sK7 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_1269]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_2232,plain,
% 3.36/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) != k1_xboole_0
% 3.36/1.01      | k1_xboole_0 = sK9
% 3.36/1.01      | k1_xboole_0 = sK8
% 3.36/1.01      | k1_xboole_0 = sK7 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_1518]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_8663,plain,
% 3.36/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
% 3.36/1.01      | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_7335,c_2207]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_8697,plain,
% 3.36/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11) ),
% 3.36/1.01      inference(global_propositional_subsumption,
% 3.36/1.01                [status(thm)],
% 3.36/1.01                [c_8667,c_36,c_35,c_34,c_2232,c_8663]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_37,negated_conjecture,
% 3.36/1.01      ( ~ m1_subset_1(X0,sK9)
% 3.36/1.01      | ~ m1_subset_1(X1,sK8)
% 3.36/1.01      | ~ m1_subset_1(X2,sK7)
% 3.36/1.01      | k4_tarski(k4_tarski(X2,X1),X0) != sK11
% 3.36/1.01      | sK10 = X0 ),
% 3.36/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_979,plain,
% 3.36/1.01      ( k4_tarski(k4_tarski(X0,X1),X2) != sK11
% 3.36/1.01      | sK10 = X2
% 3.36/1.01      | m1_subset_1(X2,sK9) != iProver_top
% 3.36/1.01      | m1_subset_1(X1,sK8) != iProver_top
% 3.36/1.01      | m1_subset_1(X0,sK7) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_8700,plain,
% 3.36/1.01      ( k4_tarski(k1_mcart_1(sK11),X0) != sK11
% 3.36/1.01      | sK10 = X0
% 3.36/1.01      | m1_subset_1(X0,sK9) != iProver_top
% 3.36/1.01      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK11)),sK7) != iProver_top
% 3.36/1.01      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK11)),sK8) != iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_8697,c_979]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_21,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.36/1.01      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
% 3.36/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_987,plain,
% 3.36/1.01      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.36/1.01      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_6529,plain,
% 3.36/1.01      ( m1_subset_1(k6_mcart_1(sK7,sK8,sK9,sK11),sK8) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_978,c_987]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_31,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.36/1.01      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.36/1.01      | k1_xboole_0 = X1
% 3.36/1.01      | k1_xboole_0 = X2
% 3.36/1.01      | k1_xboole_0 = X3 ),
% 3.36/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_981,plain,
% 3.36/1.01      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.36/1.01      | k1_xboole_0 = X1
% 3.36/1.01      | k1_xboole_0 = X0
% 3.36/1.01      | k1_xboole_0 = X2
% 3.36/1.01      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_3776,plain,
% 3.36/1.01      ( k6_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(k1_mcart_1(sK11))
% 3.36/1.01      | sK9 = k1_xboole_0
% 3.36/1.01      | sK8 = k1_xboole_0
% 3.36/1.01      | sK7 = k1_xboole_0 ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_978,c_981]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_4557,plain,
% 3.36/1.01      ( k6_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(k1_mcart_1(sK11)) ),
% 3.36/1.01      inference(global_propositional_subsumption,
% 3.36/1.01                [status(thm)],
% 3.36/1.01                [c_3776,c_36,c_35,c_34,c_52,c_53,c_1273,c_1275,c_1277]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_6568,plain,
% 3.36/1.01      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK11)),sK8) = iProver_top ),
% 3.36/1.01      inference(light_normalisation,[status(thm)],[c_6529,c_4557]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_20,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.36/1.01      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
% 3.36/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_988,plain,
% 3.36/1.01      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.36/1.01      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_7504,plain,
% 3.36/1.01      ( m1_subset_1(k5_mcart_1(sK7,sK8,sK9,sK11),sK7) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_978,c_988]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_32,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.36/1.01      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.36/1.01      | k1_xboole_0 = X1
% 3.36/1.01      | k1_xboole_0 = X2
% 3.36/1.01      | k1_xboole_0 = X3 ),
% 3.36/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_980,plain,
% 3.36/1.01      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.36/1.01      | k1_xboole_0 = X1
% 3.36/1.01      | k1_xboole_0 = X0
% 3.36/1.01      | k1_xboole_0 = X2
% 3.36/1.01      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_2168,plain,
% 3.36/1.01      ( k5_mcart_1(sK7,sK8,sK9,sK11) = k1_mcart_1(k1_mcart_1(sK11))
% 3.36/1.01      | sK9 = k1_xboole_0
% 3.36/1.01      | sK8 = k1_xboole_0
% 3.36/1.01      | sK7 = k1_xboole_0 ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_978,c_980]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_3047,plain,
% 3.36/1.01      ( k5_mcart_1(sK7,sK8,sK9,sK11) = k1_mcart_1(k1_mcart_1(sK11)) ),
% 3.36/1.01      inference(global_propositional_subsumption,
% 3.36/1.01                [status(thm)],
% 3.36/1.01                [c_2168,c_36,c_35,c_34,c_52,c_53,c_1273,c_1275,c_1277]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_7553,plain,
% 3.36/1.01      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK11)),sK7) = iProver_top ),
% 3.36/1.01      inference(light_normalisation,[status(thm)],[c_7504,c_3047]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_9526,plain,
% 3.36/1.01      ( k4_tarski(k1_mcart_1(sK11),X0) != sK11
% 3.36/1.01      | sK10 = X0
% 3.36/1.01      | m1_subset_1(X0,sK9) != iProver_top ),
% 3.36/1.01      inference(global_propositional_subsumption,
% 3.36/1.01                [status(thm)],
% 3.36/1.01                [c_8700,c_6568,c_7553]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_9535,plain,
% 3.36/1.01      ( k2_mcart_1(sK11) = sK10
% 3.36/1.01      | m1_subset_1(k2_mcart_1(sK11),sK9) != iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_6985,c_9526]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_30,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.36/1.01      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.36/1.01      | k1_xboole_0 = X1
% 3.36/1.01      | k1_xboole_0 = X2
% 3.36/1.01      | k1_xboole_0 = X3 ),
% 3.36/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_982,plain,
% 3.36/1.01      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.36/1.01      | k1_xboole_0 = X1
% 3.36/1.01      | k1_xboole_0 = X0
% 3.36/1.01      | k1_xboole_0 = X2
% 3.36/1.01      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_5102,plain,
% 3.36/1.01      ( k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11)
% 3.36/1.01      | sK9 = k1_xboole_0
% 3.36/1.01      | sK8 = k1_xboole_0
% 3.36/1.01      | sK7 = k1_xboole_0 ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_978,c_982]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1339,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,X1),X2))
% 3.36/1.01      | k7_mcart_1(sK7,X1,X2,X0) = k2_mcart_1(X0)
% 3.36/1.01      | k1_xboole_0 = X2
% 3.36/1.01      | k1_xboole_0 = X1
% 3.36/1.01      | k1_xboole_0 = sK7 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_30]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1627,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,X1),sK9))
% 3.36/1.01      | k7_mcart_1(sK7,X1,sK9,X0) = k2_mcart_1(X0)
% 3.36/1.01      | k1_xboole_0 = X1
% 3.36/1.01      | k1_xboole_0 = sK9
% 3.36/1.01      | k1_xboole_0 = sK7 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_1339]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_2802,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))
% 3.36/1.01      | k7_mcart_1(sK7,sK8,sK9,X0) = k2_mcart_1(X0)
% 3.36/1.01      | k1_xboole_0 = sK9
% 3.36/1.01      | k1_xboole_0 = sK8
% 3.36/1.01      | k1_xboole_0 = sK7 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_1627]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_4298,plain,
% 3.36/1.01      ( ~ m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))
% 3.36/1.01      | k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11)
% 3.36/1.01      | k1_xboole_0 = sK9
% 3.36/1.01      | k1_xboole_0 = sK8
% 3.36/1.01      | k1_xboole_0 = sK7 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_2802]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_5656,plain,
% 3.36/1.01      ( k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11) ),
% 3.36/1.01      inference(global_propositional_subsumption,
% 3.36/1.01                [status(thm)],
% 3.36/1.01                [c_5102,c_38,c_36,c_35,c_34,c_4298]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_33,negated_conjecture,
% 3.36/1.01      ( k7_mcart_1(sK7,sK8,sK9,sK11) != sK10 ),
% 3.36/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_5660,plain,
% 3.36/1.01      ( k2_mcart_1(sK11) != sK10 ),
% 3.36/1.01      inference(demodulation,[status(thm)],[c_5656,c_33]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_22,plain,
% 3.36/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.36/1.01      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
% 3.36/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_986,plain,
% 3.36/1.01      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.36/1.01      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_5155,plain,
% 3.36/1.01      ( m1_subset_1(k7_mcart_1(sK7,sK8,sK9,sK11),sK9) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_978,c_986]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_5659,plain,
% 3.36/1.01      ( m1_subset_1(k2_mcart_1(sK11),sK9) = iProver_top ),
% 3.36/1.01      inference(demodulation,[status(thm)],[c_5656,c_5155]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(contradiction,plain,
% 3.36/1.01      ( $false ),
% 3.36/1.01      inference(minisat,[status(thm)],[c_9535,c_5660,c_5659]) ).
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/1.01  
% 3.36/1.01  ------                               Statistics
% 3.36/1.01  
% 3.36/1.01  ------ General
% 3.36/1.01  
% 3.36/1.01  abstr_ref_over_cycles:                  0
% 3.36/1.01  abstr_ref_under_cycles:                 0
% 3.36/1.01  gc_basic_clause_elim:                   0
% 3.36/1.01  forced_gc_time:                         0
% 3.36/1.01  parsing_time:                           0.018
% 3.36/1.01  unif_index_cands_time:                  0.
% 3.36/1.01  unif_index_add_time:                    0.
% 3.36/1.01  orderings_time:                         0.
% 3.36/1.01  out_proof_time:                         0.01
% 3.36/1.01  total_time:                             0.293
% 3.36/1.01  num_of_symbols:                         54
% 3.36/1.01  num_of_terms:                           12477
% 3.36/1.01  
% 3.36/1.01  ------ Preprocessing
% 3.36/1.01  
% 3.36/1.01  num_of_splits:                          0
% 3.36/1.01  num_of_split_atoms:                     0
% 3.36/1.01  num_of_reused_defs:                     0
% 3.36/1.01  num_eq_ax_congr_red:                    75
% 3.36/1.01  num_of_sem_filtered_clauses:            1
% 3.36/1.01  num_of_subtypes:                        0
% 3.36/1.01  monotx_restored_types:                  0
% 3.36/1.01  sat_num_of_epr_types:                   0
% 3.36/1.01  sat_num_of_non_cyclic_types:            0
% 3.36/1.01  sat_guarded_non_collapsed_types:        0
% 3.36/1.01  num_pure_diseq_elim:                    0
% 3.36/1.01  simp_replaced_by:                       0
% 3.36/1.01  res_preprocessed:                       173
% 3.36/1.01  prep_upred:                             0
% 3.36/1.01  prep_unflattend:                        0
% 3.36/1.01  smt_new_axioms:                         0
% 3.36/1.01  pred_elim_cands:                        3
% 3.36/1.01  pred_elim:                              0
% 3.36/1.01  pred_elim_cl:                           0
% 3.36/1.01  pred_elim_cycles:                       2
% 3.36/1.01  merged_defs:                            0
% 3.36/1.01  merged_defs_ncl:                        0
% 3.36/1.01  bin_hyper_res:                          0
% 3.36/1.01  prep_cycles:                            4
% 3.36/1.01  pred_elim_time:                         0.001
% 3.36/1.01  splitting_time:                         0.
% 3.36/1.01  sem_filter_time:                        0.
% 3.36/1.01  monotx_time:                            0.
% 3.36/1.01  subtype_inf_time:                       0.
% 3.36/1.01  
% 3.36/1.01  ------ Problem properties
% 3.36/1.01  
% 3.36/1.01  clauses:                                38
% 3.36/1.01  conjectures:                            6
% 3.36/1.01  epr:                                    9
% 3.36/1.01  horn:                                   26
% 3.36/1.01  ground:                                 6
% 3.36/1.01  unary:                                  11
% 3.36/1.01  binary:                                 12
% 3.36/1.01  lits:                                   92
% 3.36/1.01  lits_eq:                                41
% 3.36/1.01  fd_pure:                                0
% 3.36/1.01  fd_pseudo:                              0
% 3.36/1.01  fd_cond:                                7
% 3.36/1.01  fd_pseudo_cond:                         4
% 3.36/1.01  ac_symbols:                             0
% 3.36/1.01  
% 3.36/1.01  ------ Propositional Solver
% 3.36/1.01  
% 3.36/1.01  prop_solver_calls:                      27
% 3.36/1.01  prop_fast_solver_calls:                 1082
% 3.36/1.01  smt_solver_calls:                       0
% 3.36/1.01  smt_fast_solver_calls:                  0
% 3.36/1.01  prop_num_of_clauses:                    3886
% 3.36/1.01  prop_preprocess_simplified:             10743
% 3.36/1.01  prop_fo_subsumed:                       23
% 3.36/1.01  prop_solver_time:                       0.
% 3.36/1.01  smt_solver_time:                        0.
% 3.36/1.01  smt_fast_solver_time:                   0.
% 3.36/1.01  prop_fast_solver_time:                  0.
% 3.36/1.01  prop_unsat_core_time:                   0.
% 3.36/1.01  
% 3.36/1.01  ------ QBF
% 3.36/1.01  
% 3.36/1.01  qbf_q_res:                              0
% 3.36/1.01  qbf_num_tautologies:                    0
% 3.36/1.01  qbf_prep_cycles:                        0
% 3.36/1.01  
% 3.36/1.01  ------ BMC1
% 3.36/1.01  
% 3.36/1.01  bmc1_current_bound:                     -1
% 3.36/1.01  bmc1_last_solved_bound:                 -1
% 3.36/1.01  bmc1_unsat_core_size:                   -1
% 3.36/1.01  bmc1_unsat_core_parents_size:           -1
% 3.36/1.01  bmc1_merge_next_fun:                    0
% 3.36/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.36/1.01  
% 3.36/1.01  ------ Instantiation
% 3.36/1.01  
% 3.36/1.01  inst_num_of_clauses:                    1208
% 3.36/1.01  inst_num_in_passive:                    423
% 3.36/1.01  inst_num_in_active:                     409
% 3.36/1.01  inst_num_in_unprocessed:                376
% 3.36/1.01  inst_num_of_loops:                      440
% 3.36/1.01  inst_num_of_learning_restarts:          0
% 3.36/1.01  inst_num_moves_active_passive:          30
% 3.36/1.01  inst_lit_activity:                      0
% 3.36/1.01  inst_lit_activity_moves:                0
% 3.36/1.01  inst_num_tautologies:                   0
% 3.36/1.01  inst_num_prop_implied:                  0
% 3.36/1.01  inst_num_existing_simplified:           0
% 3.36/1.01  inst_num_eq_res_simplified:             0
% 3.36/1.01  inst_num_child_elim:                    0
% 3.36/1.01  inst_num_of_dismatching_blockings:      509
% 3.36/1.01  inst_num_of_non_proper_insts:           946
% 3.36/1.01  inst_num_of_duplicates:                 0
% 3.36/1.01  inst_inst_num_from_inst_to_res:         0
% 3.36/1.01  inst_dismatching_checking_time:         0.
% 3.36/1.01  
% 3.36/1.01  ------ Resolution
% 3.36/1.01  
% 3.36/1.01  res_num_of_clauses:                     0
% 3.36/1.01  res_num_in_passive:                     0
% 3.36/1.01  res_num_in_active:                      0
% 3.36/1.01  res_num_of_loops:                       177
% 3.36/1.01  res_forward_subset_subsumed:            15
% 3.36/1.01  res_backward_subset_subsumed:           0
% 3.36/1.01  res_forward_subsumed:                   0
% 3.36/1.01  res_backward_subsumed:                  0
% 3.36/1.01  res_forward_subsumption_resolution:     0
% 3.36/1.01  res_backward_subsumption_resolution:    0
% 3.36/1.01  res_clause_to_clause_subsumption:       423
% 3.36/1.01  res_orphan_elimination:                 0
% 3.36/1.01  res_tautology_del:                      2
% 3.36/1.01  res_num_eq_res_simplified:              0
% 3.36/1.01  res_num_sel_changes:                    0
% 3.36/1.01  res_moves_from_active_to_pass:          0
% 3.36/1.01  
% 3.36/1.01  ------ Superposition
% 3.36/1.01  
% 3.36/1.01  sup_time_total:                         0.
% 3.36/1.01  sup_time_generating:                    0.
% 3.36/1.01  sup_time_sim_full:                      0.
% 3.36/1.01  sup_time_sim_immed:                     0.
% 3.36/1.01  
% 3.36/1.01  sup_num_of_clauses:                     236
% 3.36/1.01  sup_num_in_active:                      77
% 3.36/1.01  sup_num_in_passive:                     159
% 3.36/1.01  sup_num_of_loops:                       87
% 3.36/1.01  sup_fw_superposition:                   142
% 3.36/1.01  sup_bw_superposition:                   129
% 3.36/1.01  sup_immediate_simplified:               35
% 3.36/1.01  sup_given_eliminated:                   0
% 3.36/1.01  comparisons_done:                       0
% 3.36/1.01  comparisons_avoided:                    11
% 3.36/1.01  
% 3.36/1.01  ------ Simplifications
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  sim_fw_subset_subsumed:                 19
% 3.36/1.01  sim_bw_subset_subsumed:                 13
% 3.36/1.01  sim_fw_subsumed:                        2
% 3.36/1.01  sim_bw_subsumed:                        1
% 3.36/1.01  sim_fw_subsumption_res:                 0
% 3.36/1.01  sim_bw_subsumption_res:                 0
% 3.36/1.01  sim_tautology_del:                      4
% 3.36/1.01  sim_eq_tautology_del:                   17
% 3.36/1.01  sim_eq_res_simp:                        0
% 3.36/1.01  sim_fw_demodulated:                     12
% 3.36/1.01  sim_bw_demodulated:                     2
% 3.36/1.01  sim_light_normalised:                   5
% 3.36/1.01  sim_joinable_taut:                      0
% 3.36/1.01  sim_joinable_simp:                      0
% 3.36/1.01  sim_ac_normalised:                      0
% 3.36/1.01  sim_smt_subsumption:                    0
% 3.36/1.01  
%------------------------------------------------------------------------------
