%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:04 EST 2020

% Result     : Theorem 7.20s
% Output     : CNFRefutation 7.20s
% Verified   : 
% Statistics : Number of formulae       :  209 (13009 expanded)
%              Number of clauses        :  134 (3828 expanded)
%              Number of leaves         :   19 (2928 expanded)
%              Depth                    :   37
%              Number of atoms          :  610 (54772 expanded)
%              Number of equality atoms :  490 (39467 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f36,plain,
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
   => ( k7_mcart_1(sK3,sK4,sK5,sK7) != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK6 = X7
                  | k3_mcart_1(X5,X6,X7) != sK7
                  | ~ m1_subset_1(X7,sK5) )
              | ~ m1_subset_1(X6,sK4) )
          | ~ m1_subset_1(X5,sK3) )
      & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK6 = X7
                | k3_mcart_1(X5,X6,X7) != sK7
                | ~ m1_subset_1(X7,sK5) )
            | ~ m1_subset_1(X6,sK4) )
        | ~ m1_subset_1(X5,sK3) )
    & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f27,f36])).

fof(f62,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f78,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f62,f45])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK1(X0),sK2(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK1(X0),sK2(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f32])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK1(X0),sK2(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f34])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f57,f68])).

fof(f83,plain,(
    ! [X2,X0,X3] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3) ),
    inference(equality_resolution,[],[f74])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f55,f68])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f56,f68])).

fof(f84,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f75])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f82,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f73])).

fof(f10,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X7
      | k3_mcart_1(X5,X6,X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(definition_unfolding,[],[f63,f44])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f54,f45])).

fof(f67,plain,(
    k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_503,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_511,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3510,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_503,c_511])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_513,plain,
    ( k4_tarski(sK1(X0),sK2(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3743,plain,
    ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3510,c_513])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_514,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3801,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(sK1(sK7),sK2(sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_3743,c_514])).

cnf(c_4659,plain,
    ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7
    | m1_subset_1(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3801,c_503])).

cnf(c_16,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_508,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X0,k2_zfmisc_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3461,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0
    | k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_508])).

cnf(c_5086,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | k4_tarski(sK1(sK7),sK2(sK7)) = sK7
    | k1_xboole_0 = X2 ),
    inference(superposition,[status(thm)],[c_4659,c_3461])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_509,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5288,plain,
    ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | k4_tarski(sK1(sK7),sK2(sK7)) = sK7
    | k1_xboole_0 = X0
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5086,c_509])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_18,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_250,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_685,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_686,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_687,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_688,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_689,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_690,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_4651,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | k4_tarski(sK1(sK7),sK2(sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_3801,c_18])).

cnf(c_15,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_996,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15,c_15])).

cnf(c_4700,plain,
    ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4651,c_996])).

cnf(c_4701,plain,
    ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4700])).

cnf(c_7064,plain,
    ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5288,c_24,c_23,c_22,c_33,c_34,c_686,c_688,c_690,c_4701])).

cnf(c_8,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_19,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_542,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_8,c_19])).

cnf(c_7263,plain,
    ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7
    | k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_7064,c_542])).

cnf(c_7458,plain,
    ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7263,c_7064])).

cnf(c_20,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_7485,plain,
    ( k1_mcart_1(sK7) = sK1(sK7) ),
    inference(superposition,[status(thm)],[c_7458,c_20])).

cnf(c_3745,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3510,c_509])).

cnf(c_3816,plain,
    ( k4_tarski(sK1(k1_mcart_1(sK7)),sK2(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3745,c_513])).

cnf(c_8464,plain,
    ( k4_tarski(sK1(sK1(sK7)),sK2(sK1(sK7))) = sK1(sK7)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7485,c_3816])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_516,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2614,plain,
    ( r2_hidden(k1_mcart_1(sK0(k2_zfmisc_1(X0,X1))),X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_516,c_509])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_515,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12508,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2614,c_515])).

cnf(c_12668,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12508,c_514])).

cnf(c_17246,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) = k1_xboole_0
    | k4_tarski(sK1(sK1(sK7)),sK2(sK1(sK7))) = sK1(sK7) ),
    inference(superposition,[status(thm)],[c_8464,c_12668])).

cnf(c_24388,plain,
    ( k4_tarski(sK1(sK1(sK7)),sK2(sK1(sK7))) = sK1(sK7)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_17246,c_18])).

cnf(c_25805,plain,
    ( k4_tarski(sK1(sK1(sK7)),sK2(sK1(sK7))) = sK1(sK7)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24388,c_24,c_23,c_22,c_33,c_34,c_686,c_688,c_690])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ m1_subset_1(X1,sK4)
    | ~ m1_subset_1(X2,sK3)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK7
    | sK6 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_504,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
    | sK6 = X2
    | m1_subset_1(X2,sK5) != iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26314,plain,
    ( k4_tarski(sK1(sK7),X0) != sK7
    | sK6 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK2(sK1(sK7)),sK4) != iProver_top
    | m1_subset_1(sK1(sK1(sK7)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_25805,c_504])).

cnf(c_6183,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(sK1(k1_mcart_1(sK7)),sK2(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
    inference(superposition,[status(thm)],[c_3816,c_514])).

cnf(c_13432,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(sK1(sK1(sK7)),sK2(sK1(sK7))) = sK1(sK7) ),
    inference(light_normalisation,[status(thm)],[c_6183,c_7485])).

cnf(c_13441,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7)) ),
    inference(superposition,[status(thm)],[c_13432,c_20])).

cnf(c_13877,plain,
    ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
    | m1_subset_1(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13441,c_503])).

cnf(c_14751,plain,
    ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
    | r2_hidden(sK7,k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13877,c_511])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_510,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2998,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_510])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_512,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3170,plain,
    ( m1_subset_1(k2_mcart_1(X0),X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2998,c_512])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_507,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3301,plain,
    ( k7_mcart_1(X0,X1,X2,k2_mcart_1(X3)) = k2_mcart_1(k2_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | r2_hidden(X3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3170,c_507])).

cnf(c_19066,plain,
    ( k7_mcart_1(X0,X1,X2,k2_mcart_1(sK7)) = k2_mcart_1(k2_mcart_1(sK7))
    | k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14751,c_3301])).

cnf(c_7486,plain,
    ( k2_mcart_1(sK7) = sK2(sK7) ),
    inference(superposition,[status(thm)],[c_7458,c_19])).

cnf(c_19145,plain,
    ( k7_mcart_1(X0,X1,X2,sK2(sK7)) = k2_mcart_1(sK2(sK7))
    | k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19066,c_7486])).

cnf(c_13868,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_13441,c_18])).

cnf(c_13922,plain,
    ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13868,c_996])).

cnf(c_13923,plain,
    ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_13922])).

cnf(c_19826,plain,
    ( k1_xboole_0 = X0
    | k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19145,c_24,c_23,c_22,c_33,c_34,c_686,c_688,c_690,c_13923])).

cnf(c_19827,plain,
    ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_19826])).

cnf(c_3818,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3745,c_509])).

cnf(c_6137,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3818,c_514])).

cnf(c_11601,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | r2_hidden(k1_mcart_1(sK1(sK7)),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6137,c_7485])).

cnf(c_20225,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k1_xboole_0 = X0
    | r2_hidden(sK1(sK1(sK7)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_19827,c_11601])).

cnf(c_702,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,X0),X1),X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_899,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),X0),X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_1378,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_20197,plain,
    ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
    | k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_19827,c_542])).

cnf(c_20360,plain,
    ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20197,c_19827])).

cnf(c_8466,plain,
    ( r2_hidden(k1_mcart_1(sK1(sK7)),sK3) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7485,c_3818])).

cnf(c_20943,plain,
    ( r2_hidden(sK1(sK1(sK7)),sK3) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20360,c_8466])).

cnf(c_21762,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) = k1_xboole_0
    | r2_hidden(sK1(sK1(sK7)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_20943,c_12668])).

cnf(c_23198,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(sK1(sK7)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20225,c_24,c_23,c_22,c_1378,c_21762])).

cnf(c_23205,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(sK1(sK1(sK7)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_23198,c_512])).

cnf(c_13442,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7)) ),
    inference(superposition,[status(thm)],[c_13432,c_19])).

cnf(c_14090,plain,
    ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
    | m1_subset_1(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13442,c_503])).

cnf(c_14846,plain,
    ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
    | r2_hidden(sK7,k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14090,c_511])).

cnf(c_19065,plain,
    ( k7_mcart_1(X0,X1,X2,k2_mcart_1(sK7)) = k2_mcart_1(k2_mcart_1(sK7))
    | k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14846,c_3301])).

cnf(c_19158,plain,
    ( k7_mcart_1(X0,X1,X2,sK2(sK7)) = k2_mcart_1(sK2(sK7))
    | k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19065,c_7486])).

cnf(c_14081,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_13442,c_18])).

cnf(c_14135,plain,
    ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14081,c_996])).

cnf(c_14136,plain,
    ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_14135])).

cnf(c_20373,plain,
    ( k1_xboole_0 = X0
    | k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19158,c_24,c_23,c_22,c_33,c_34,c_686,c_688,c_690,c_14136])).

cnf(c_20374,plain,
    ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_20373])).

cnf(c_3817,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3745,c_510])).

cnf(c_6121,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3817,c_514])).

cnf(c_11584,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK1(sK7)),sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6121,c_7485])).

cnf(c_20765,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k1_xboole_0 = X0
    | r2_hidden(sK2(sK1(sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_20374,c_11584])).

cnf(c_20735,plain,
    ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
    | k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_20374,c_542])).

cnf(c_20912,plain,
    ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20735,c_20374])).

cnf(c_8467,plain,
    ( r2_hidden(k2_mcart_1(sK1(sK7)),sK4) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7485,c_3817])).

cnf(c_21020,plain,
    ( r2_hidden(sK2(sK1(sK7)),sK4) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20912,c_8467])).

cnf(c_21786,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) = k1_xboole_0
    | r2_hidden(sK2(sK1(sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_21020,c_12668])).

cnf(c_24277,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(sK1(sK7)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20765,c_24,c_23,c_22,c_1378,c_21786])).

cnf(c_24284,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(sK2(sK1(sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_24277,c_512])).

cnf(c_26481,plain,
    ( k4_tarski(sK1(sK7),X0) != sK7
    | sK6 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_26314,c_23205,c_24284])).

cnf(c_26483,plain,
    ( sK2(sK7) = sK6
    | k1_xboole_0 = X0
    | m1_subset_1(sK2(sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7458,c_26481])).

cnf(c_3026,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_503,c_507])).

cnf(c_3275,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3026,c_24,c_23,c_22,c_33,c_34,c_686,c_688,c_690])).

cnf(c_21,negated_conjecture,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3278,plain,
    ( k2_mcart_1(sK7) != sK6 ),
    inference(demodulation,[status(thm)],[c_3275,c_21])).

cnf(c_8523,plain,
    ( sK2(sK7) != sK6 ),
    inference(demodulation,[status(thm)],[c_7486,c_3278])).

cnf(c_3744,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK5) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3510,c_510])).

cnf(c_8521,plain,
    ( r2_hidden(sK2(sK7),sK5) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7486,c_3744])).

cnf(c_13267,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) = k1_xboole_0
    | r2_hidden(sK2(sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_8521,c_12668])).

cnf(c_13402,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) = k1_xboole_0
    | m1_subset_1(sK2(sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_13267,c_512])).

cnf(c_26490,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26483,c_24,c_23,c_22,c_1378,c_8523,c_13402])).

cnf(c_26595,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_26490,c_22])).

cnf(c_26898,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_26595])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:15:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.20/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.20/1.49  
% 7.20/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.20/1.49  
% 7.20/1.49  ------  iProver source info
% 7.20/1.49  
% 7.20/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.20/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.20/1.49  git: non_committed_changes: false
% 7.20/1.49  git: last_make_outside_of_git: false
% 7.20/1.49  
% 7.20/1.49  ------ 
% 7.20/1.49  
% 7.20/1.49  ------ Input Options
% 7.20/1.49  
% 7.20/1.49  --out_options                           all
% 7.20/1.49  --tptp_safe_out                         true
% 7.20/1.49  --problem_path                          ""
% 7.20/1.49  --include_path                          ""
% 7.20/1.49  --clausifier                            res/vclausify_rel
% 7.20/1.49  --clausifier_options                    --mode clausify
% 7.20/1.49  --stdin                                 false
% 7.20/1.49  --stats_out                             all
% 7.20/1.49  
% 7.20/1.49  ------ General Options
% 7.20/1.49  
% 7.20/1.49  --fof                                   false
% 7.20/1.49  --time_out_real                         305.
% 7.20/1.49  --time_out_virtual                      -1.
% 7.20/1.49  --symbol_type_check                     false
% 7.20/1.49  --clausify_out                          false
% 7.20/1.49  --sig_cnt_out                           false
% 7.20/1.49  --trig_cnt_out                          false
% 7.20/1.49  --trig_cnt_out_tolerance                1.
% 7.20/1.49  --trig_cnt_out_sk_spl                   false
% 7.20/1.49  --abstr_cl_out                          false
% 7.20/1.49  
% 7.20/1.49  ------ Global Options
% 7.20/1.49  
% 7.20/1.49  --schedule                              default
% 7.20/1.49  --add_important_lit                     false
% 7.20/1.49  --prop_solver_per_cl                    1000
% 7.20/1.49  --min_unsat_core                        false
% 7.20/1.49  --soft_assumptions                      false
% 7.20/1.49  --soft_lemma_size                       3
% 7.20/1.49  --prop_impl_unit_size                   0
% 7.20/1.49  --prop_impl_unit                        []
% 7.20/1.49  --share_sel_clauses                     true
% 7.20/1.49  --reset_solvers                         false
% 7.20/1.49  --bc_imp_inh                            [conj_cone]
% 7.20/1.49  --conj_cone_tolerance                   3.
% 7.20/1.49  --extra_neg_conj                        none
% 7.20/1.49  --large_theory_mode                     true
% 7.20/1.49  --prolific_symb_bound                   200
% 7.20/1.49  --lt_threshold                          2000
% 7.20/1.49  --clause_weak_htbl                      true
% 7.20/1.49  --gc_record_bc_elim                     false
% 7.20/1.49  
% 7.20/1.49  ------ Preprocessing Options
% 7.20/1.49  
% 7.20/1.49  --preprocessing_flag                    true
% 7.20/1.49  --time_out_prep_mult                    0.1
% 7.20/1.49  --splitting_mode                        input
% 7.20/1.49  --splitting_grd                         true
% 7.20/1.49  --splitting_cvd                         false
% 7.20/1.49  --splitting_cvd_svl                     false
% 7.20/1.49  --splitting_nvd                         32
% 7.20/1.49  --sub_typing                            true
% 7.20/1.49  --prep_gs_sim                           true
% 7.20/1.49  --prep_unflatten                        true
% 7.20/1.49  --prep_res_sim                          true
% 7.20/1.49  --prep_upred                            true
% 7.20/1.49  --prep_sem_filter                       exhaustive
% 7.20/1.49  --prep_sem_filter_out                   false
% 7.20/1.49  --pred_elim                             true
% 7.20/1.49  --res_sim_input                         true
% 7.20/1.49  --eq_ax_congr_red                       true
% 7.20/1.49  --pure_diseq_elim                       true
% 7.20/1.49  --brand_transform                       false
% 7.20/1.49  --non_eq_to_eq                          false
% 7.20/1.49  --prep_def_merge                        true
% 7.20/1.49  --prep_def_merge_prop_impl              false
% 7.20/1.49  --prep_def_merge_mbd                    true
% 7.20/1.49  --prep_def_merge_tr_red                 false
% 7.20/1.49  --prep_def_merge_tr_cl                  false
% 7.20/1.49  --smt_preprocessing                     true
% 7.20/1.49  --smt_ac_axioms                         fast
% 7.20/1.49  --preprocessed_out                      false
% 7.20/1.49  --preprocessed_stats                    false
% 7.20/1.49  
% 7.20/1.49  ------ Abstraction refinement Options
% 7.20/1.49  
% 7.20/1.49  --abstr_ref                             []
% 7.20/1.49  --abstr_ref_prep                        false
% 7.20/1.49  --abstr_ref_until_sat                   false
% 7.20/1.49  --abstr_ref_sig_restrict                funpre
% 7.20/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.20/1.49  --abstr_ref_under                       []
% 7.20/1.49  
% 7.20/1.49  ------ SAT Options
% 7.20/1.49  
% 7.20/1.49  --sat_mode                              false
% 7.20/1.49  --sat_fm_restart_options                ""
% 7.20/1.49  --sat_gr_def                            false
% 7.20/1.49  --sat_epr_types                         true
% 7.20/1.49  --sat_non_cyclic_types                  false
% 7.20/1.49  --sat_finite_models                     false
% 7.20/1.49  --sat_fm_lemmas                         false
% 7.20/1.49  --sat_fm_prep                           false
% 7.20/1.49  --sat_fm_uc_incr                        true
% 7.20/1.49  --sat_out_model                         small
% 7.20/1.49  --sat_out_clauses                       false
% 7.20/1.49  
% 7.20/1.49  ------ QBF Options
% 7.20/1.49  
% 7.20/1.49  --qbf_mode                              false
% 7.20/1.49  --qbf_elim_univ                         false
% 7.20/1.49  --qbf_dom_inst                          none
% 7.20/1.49  --qbf_dom_pre_inst                      false
% 7.20/1.49  --qbf_sk_in                             false
% 7.20/1.49  --qbf_pred_elim                         true
% 7.20/1.49  --qbf_split                             512
% 7.20/1.49  
% 7.20/1.49  ------ BMC1 Options
% 7.20/1.49  
% 7.20/1.49  --bmc1_incremental                      false
% 7.20/1.49  --bmc1_axioms                           reachable_all
% 7.20/1.49  --bmc1_min_bound                        0
% 7.20/1.49  --bmc1_max_bound                        -1
% 7.20/1.49  --bmc1_max_bound_default                -1
% 7.20/1.49  --bmc1_symbol_reachability              true
% 7.20/1.49  --bmc1_property_lemmas                  false
% 7.20/1.49  --bmc1_k_induction                      false
% 7.20/1.49  --bmc1_non_equiv_states                 false
% 7.20/1.49  --bmc1_deadlock                         false
% 7.20/1.49  --bmc1_ucm                              false
% 7.20/1.49  --bmc1_add_unsat_core                   none
% 7.20/1.49  --bmc1_unsat_core_children              false
% 7.20/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.20/1.49  --bmc1_out_stat                         full
% 7.20/1.49  --bmc1_ground_init                      false
% 7.20/1.49  --bmc1_pre_inst_next_state              false
% 7.20/1.49  --bmc1_pre_inst_state                   false
% 7.20/1.49  --bmc1_pre_inst_reach_state             false
% 7.20/1.49  --bmc1_out_unsat_core                   false
% 7.20/1.49  --bmc1_aig_witness_out                  false
% 7.20/1.49  --bmc1_verbose                          false
% 7.20/1.49  --bmc1_dump_clauses_tptp                false
% 7.20/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.20/1.49  --bmc1_dump_file                        -
% 7.20/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.20/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.20/1.49  --bmc1_ucm_extend_mode                  1
% 7.20/1.49  --bmc1_ucm_init_mode                    2
% 7.20/1.49  --bmc1_ucm_cone_mode                    none
% 7.20/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.20/1.49  --bmc1_ucm_relax_model                  4
% 7.20/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.20/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.20/1.49  --bmc1_ucm_layered_model                none
% 7.20/1.49  --bmc1_ucm_max_lemma_size               10
% 7.20/1.49  
% 7.20/1.49  ------ AIG Options
% 7.20/1.49  
% 7.20/1.49  --aig_mode                              false
% 7.20/1.49  
% 7.20/1.49  ------ Instantiation Options
% 7.20/1.49  
% 7.20/1.49  --instantiation_flag                    true
% 7.20/1.49  --inst_sos_flag                         false
% 7.20/1.49  --inst_sos_phase                        true
% 7.20/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.20/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.20/1.49  --inst_lit_sel_side                     num_symb
% 7.20/1.49  --inst_solver_per_active                1400
% 7.20/1.49  --inst_solver_calls_frac                1.
% 7.20/1.49  --inst_passive_queue_type               priority_queues
% 7.20/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.20/1.49  --inst_passive_queues_freq              [25;2]
% 7.20/1.49  --inst_dismatching                      true
% 7.20/1.49  --inst_eager_unprocessed_to_passive     true
% 7.20/1.49  --inst_prop_sim_given                   true
% 7.20/1.49  --inst_prop_sim_new                     false
% 7.20/1.49  --inst_subs_new                         false
% 7.20/1.49  --inst_eq_res_simp                      false
% 7.20/1.49  --inst_subs_given                       false
% 7.20/1.49  --inst_orphan_elimination               true
% 7.20/1.49  --inst_learning_loop_flag               true
% 7.20/1.49  --inst_learning_start                   3000
% 7.20/1.49  --inst_learning_factor                  2
% 7.20/1.49  --inst_start_prop_sim_after_learn       3
% 7.20/1.49  --inst_sel_renew                        solver
% 7.20/1.49  --inst_lit_activity_flag                true
% 7.20/1.49  --inst_restr_to_given                   false
% 7.20/1.49  --inst_activity_threshold               500
% 7.20/1.49  --inst_out_proof                        true
% 7.20/1.49  
% 7.20/1.49  ------ Resolution Options
% 7.20/1.49  
% 7.20/1.49  --resolution_flag                       true
% 7.20/1.49  --res_lit_sel                           adaptive
% 7.20/1.49  --res_lit_sel_side                      none
% 7.20/1.49  --res_ordering                          kbo
% 7.20/1.49  --res_to_prop_solver                    active
% 7.20/1.49  --res_prop_simpl_new                    false
% 7.20/1.49  --res_prop_simpl_given                  true
% 7.20/1.49  --res_passive_queue_type                priority_queues
% 7.20/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.20/1.49  --res_passive_queues_freq               [15;5]
% 7.20/1.49  --res_forward_subs                      full
% 7.20/1.49  --res_backward_subs                     full
% 7.20/1.49  --res_forward_subs_resolution           true
% 7.20/1.49  --res_backward_subs_resolution          true
% 7.20/1.49  --res_orphan_elimination                true
% 7.20/1.49  --res_time_limit                        2.
% 7.20/1.49  --res_out_proof                         true
% 7.20/1.49  
% 7.20/1.49  ------ Superposition Options
% 7.20/1.49  
% 7.20/1.49  --superposition_flag                    true
% 7.20/1.49  --sup_passive_queue_type                priority_queues
% 7.20/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.20/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.20/1.49  --demod_completeness_check              fast
% 7.20/1.49  --demod_use_ground                      true
% 7.20/1.49  --sup_to_prop_solver                    passive
% 7.20/1.49  --sup_prop_simpl_new                    true
% 7.20/1.49  --sup_prop_simpl_given                  true
% 7.20/1.49  --sup_fun_splitting                     false
% 7.20/1.49  --sup_smt_interval                      50000
% 7.20/1.49  
% 7.20/1.49  ------ Superposition Simplification Setup
% 7.20/1.49  
% 7.20/1.49  --sup_indices_passive                   []
% 7.20/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.20/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.20/1.49  --sup_full_bw                           [BwDemod]
% 7.20/1.49  --sup_immed_triv                        [TrivRules]
% 7.20/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.20/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.20/1.49  --sup_immed_bw_main                     []
% 7.20/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.20/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.20/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.20/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.20/1.49  
% 7.20/1.49  ------ Combination Options
% 7.20/1.49  
% 7.20/1.49  --comb_res_mult                         3
% 7.20/1.49  --comb_sup_mult                         2
% 7.20/1.49  --comb_inst_mult                        10
% 7.20/1.49  
% 7.20/1.49  ------ Debug Options
% 7.20/1.49  
% 7.20/1.49  --dbg_backtrace                         false
% 7.20/1.49  --dbg_dump_prop_clauses                 false
% 7.20/1.49  --dbg_dump_prop_clauses_file            -
% 7.20/1.49  --dbg_out_stat                          false
% 7.20/1.49  ------ Parsing...
% 7.20/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.20/1.49  
% 7.20/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.20/1.49  
% 7.20/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.20/1.49  
% 7.20/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.20/1.49  ------ Proving...
% 7.20/1.49  ------ Problem Properties 
% 7.20/1.49  
% 7.20/1.49  
% 7.20/1.49  clauses                                 27
% 7.20/1.49  conjectures                             6
% 7.20/1.49  EPR                                     7
% 7.20/1.49  Horn                                    20
% 7.20/1.49  unary                                   13
% 7.20/1.49  binary                                  7
% 7.20/1.49  lits                                    59
% 7.20/1.49  lits eq                                 36
% 7.20/1.49  fd_pure                                 0
% 7.20/1.49  fd_pseudo                               0
% 7.20/1.49  fd_cond                                 6
% 7.20/1.49  fd_pseudo_cond                          0
% 7.20/1.49  AC symbols                              0
% 7.20/1.49  
% 7.20/1.49  ------ Schedule dynamic 5 is on 
% 7.20/1.49  
% 7.20/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.20/1.49  
% 7.20/1.49  
% 7.20/1.49  ------ 
% 7.20/1.49  Current options:
% 7.20/1.49  ------ 
% 7.20/1.49  
% 7.20/1.49  ------ Input Options
% 7.20/1.49  
% 7.20/1.49  --out_options                           all
% 7.20/1.49  --tptp_safe_out                         true
% 7.20/1.49  --problem_path                          ""
% 7.20/1.49  --include_path                          ""
% 7.20/1.49  --clausifier                            res/vclausify_rel
% 7.20/1.49  --clausifier_options                    --mode clausify
% 7.20/1.49  --stdin                                 false
% 7.20/1.49  --stats_out                             all
% 7.20/1.49  
% 7.20/1.49  ------ General Options
% 7.20/1.49  
% 7.20/1.49  --fof                                   false
% 7.20/1.49  --time_out_real                         305.
% 7.20/1.49  --time_out_virtual                      -1.
% 7.20/1.49  --symbol_type_check                     false
% 7.20/1.49  --clausify_out                          false
% 7.20/1.49  --sig_cnt_out                           false
% 7.20/1.49  --trig_cnt_out                          false
% 7.20/1.49  --trig_cnt_out_tolerance                1.
% 7.20/1.49  --trig_cnt_out_sk_spl                   false
% 7.20/1.49  --abstr_cl_out                          false
% 7.20/1.49  
% 7.20/1.49  ------ Global Options
% 7.20/1.49  
% 7.20/1.49  --schedule                              default
% 7.20/1.49  --add_important_lit                     false
% 7.20/1.49  --prop_solver_per_cl                    1000
% 7.20/1.49  --min_unsat_core                        false
% 7.20/1.49  --soft_assumptions                      false
% 7.20/1.49  --soft_lemma_size                       3
% 7.20/1.49  --prop_impl_unit_size                   0
% 7.20/1.49  --prop_impl_unit                        []
% 7.20/1.49  --share_sel_clauses                     true
% 7.20/1.49  --reset_solvers                         false
% 7.20/1.49  --bc_imp_inh                            [conj_cone]
% 7.20/1.49  --conj_cone_tolerance                   3.
% 7.20/1.49  --extra_neg_conj                        none
% 7.20/1.49  --large_theory_mode                     true
% 7.20/1.49  --prolific_symb_bound                   200
% 7.20/1.49  --lt_threshold                          2000
% 7.20/1.49  --clause_weak_htbl                      true
% 7.20/1.49  --gc_record_bc_elim                     false
% 7.20/1.49  
% 7.20/1.49  ------ Preprocessing Options
% 7.20/1.49  
% 7.20/1.49  --preprocessing_flag                    true
% 7.20/1.49  --time_out_prep_mult                    0.1
% 7.20/1.49  --splitting_mode                        input
% 7.20/1.49  --splitting_grd                         true
% 7.20/1.49  --splitting_cvd                         false
% 7.20/1.49  --splitting_cvd_svl                     false
% 7.20/1.49  --splitting_nvd                         32
% 7.20/1.49  --sub_typing                            true
% 7.20/1.49  --prep_gs_sim                           true
% 7.20/1.49  --prep_unflatten                        true
% 7.20/1.49  --prep_res_sim                          true
% 7.20/1.49  --prep_upred                            true
% 7.20/1.49  --prep_sem_filter                       exhaustive
% 7.20/1.49  --prep_sem_filter_out                   false
% 7.20/1.49  --pred_elim                             true
% 7.20/1.49  --res_sim_input                         true
% 7.20/1.49  --eq_ax_congr_red                       true
% 7.20/1.49  --pure_diseq_elim                       true
% 7.20/1.49  --brand_transform                       false
% 7.20/1.49  --non_eq_to_eq                          false
% 7.20/1.49  --prep_def_merge                        true
% 7.20/1.49  --prep_def_merge_prop_impl              false
% 7.20/1.49  --prep_def_merge_mbd                    true
% 7.20/1.49  --prep_def_merge_tr_red                 false
% 7.20/1.49  --prep_def_merge_tr_cl                  false
% 7.20/1.49  --smt_preprocessing                     true
% 7.20/1.49  --smt_ac_axioms                         fast
% 7.20/1.49  --preprocessed_out                      false
% 7.20/1.49  --preprocessed_stats                    false
% 7.20/1.49  
% 7.20/1.49  ------ Abstraction refinement Options
% 7.20/1.49  
% 7.20/1.49  --abstr_ref                             []
% 7.20/1.49  --abstr_ref_prep                        false
% 7.20/1.49  --abstr_ref_until_sat                   false
% 7.20/1.49  --abstr_ref_sig_restrict                funpre
% 7.20/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.20/1.49  --abstr_ref_under                       []
% 7.20/1.49  
% 7.20/1.49  ------ SAT Options
% 7.20/1.49  
% 7.20/1.49  --sat_mode                              false
% 7.20/1.49  --sat_fm_restart_options                ""
% 7.20/1.49  --sat_gr_def                            false
% 7.20/1.49  --sat_epr_types                         true
% 7.20/1.49  --sat_non_cyclic_types                  false
% 7.20/1.49  --sat_finite_models                     false
% 7.20/1.49  --sat_fm_lemmas                         false
% 7.20/1.49  --sat_fm_prep                           false
% 7.20/1.49  --sat_fm_uc_incr                        true
% 7.20/1.49  --sat_out_model                         small
% 7.20/1.49  --sat_out_clauses                       false
% 7.20/1.49  
% 7.20/1.49  ------ QBF Options
% 7.20/1.49  
% 7.20/1.49  --qbf_mode                              false
% 7.20/1.49  --qbf_elim_univ                         false
% 7.20/1.49  --qbf_dom_inst                          none
% 7.20/1.49  --qbf_dom_pre_inst                      false
% 7.20/1.49  --qbf_sk_in                             false
% 7.20/1.49  --qbf_pred_elim                         true
% 7.20/1.49  --qbf_split                             512
% 7.20/1.49  
% 7.20/1.49  ------ BMC1 Options
% 7.20/1.49  
% 7.20/1.49  --bmc1_incremental                      false
% 7.20/1.49  --bmc1_axioms                           reachable_all
% 7.20/1.49  --bmc1_min_bound                        0
% 7.20/1.49  --bmc1_max_bound                        -1
% 7.20/1.49  --bmc1_max_bound_default                -1
% 7.20/1.49  --bmc1_symbol_reachability              true
% 7.20/1.49  --bmc1_property_lemmas                  false
% 7.20/1.50  --bmc1_k_induction                      false
% 7.20/1.50  --bmc1_non_equiv_states                 false
% 7.20/1.50  --bmc1_deadlock                         false
% 7.20/1.50  --bmc1_ucm                              false
% 7.20/1.50  --bmc1_add_unsat_core                   none
% 7.20/1.50  --bmc1_unsat_core_children              false
% 7.20/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.20/1.50  --bmc1_out_stat                         full
% 7.20/1.50  --bmc1_ground_init                      false
% 7.20/1.50  --bmc1_pre_inst_next_state              false
% 7.20/1.50  --bmc1_pre_inst_state                   false
% 7.20/1.50  --bmc1_pre_inst_reach_state             false
% 7.20/1.50  --bmc1_out_unsat_core                   false
% 7.20/1.50  --bmc1_aig_witness_out                  false
% 7.20/1.50  --bmc1_verbose                          false
% 7.20/1.50  --bmc1_dump_clauses_tptp                false
% 7.20/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.20/1.50  --bmc1_dump_file                        -
% 7.20/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.20/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.20/1.50  --bmc1_ucm_extend_mode                  1
% 7.20/1.50  --bmc1_ucm_init_mode                    2
% 7.20/1.50  --bmc1_ucm_cone_mode                    none
% 7.20/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.20/1.50  --bmc1_ucm_relax_model                  4
% 7.20/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.20/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.20/1.50  --bmc1_ucm_layered_model                none
% 7.20/1.50  --bmc1_ucm_max_lemma_size               10
% 7.20/1.50  
% 7.20/1.50  ------ AIG Options
% 7.20/1.50  
% 7.20/1.50  --aig_mode                              false
% 7.20/1.50  
% 7.20/1.50  ------ Instantiation Options
% 7.20/1.50  
% 7.20/1.50  --instantiation_flag                    true
% 7.20/1.50  --inst_sos_flag                         false
% 7.20/1.50  --inst_sos_phase                        true
% 7.20/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.20/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.20/1.50  --inst_lit_sel_side                     none
% 7.20/1.50  --inst_solver_per_active                1400
% 7.20/1.50  --inst_solver_calls_frac                1.
% 7.20/1.50  --inst_passive_queue_type               priority_queues
% 7.20/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.20/1.50  --inst_passive_queues_freq              [25;2]
% 7.20/1.50  --inst_dismatching                      true
% 7.20/1.50  --inst_eager_unprocessed_to_passive     true
% 7.20/1.50  --inst_prop_sim_given                   true
% 7.20/1.50  --inst_prop_sim_new                     false
% 7.20/1.50  --inst_subs_new                         false
% 7.20/1.50  --inst_eq_res_simp                      false
% 7.20/1.50  --inst_subs_given                       false
% 7.20/1.50  --inst_orphan_elimination               true
% 7.20/1.50  --inst_learning_loop_flag               true
% 7.20/1.50  --inst_learning_start                   3000
% 7.20/1.50  --inst_learning_factor                  2
% 7.20/1.50  --inst_start_prop_sim_after_learn       3
% 7.20/1.50  --inst_sel_renew                        solver
% 7.20/1.50  --inst_lit_activity_flag                true
% 7.20/1.50  --inst_restr_to_given                   false
% 7.20/1.50  --inst_activity_threshold               500
% 7.20/1.50  --inst_out_proof                        true
% 7.20/1.50  
% 7.20/1.50  ------ Resolution Options
% 7.20/1.50  
% 7.20/1.50  --resolution_flag                       false
% 7.20/1.50  --res_lit_sel                           adaptive
% 7.20/1.50  --res_lit_sel_side                      none
% 7.20/1.50  --res_ordering                          kbo
% 7.20/1.50  --res_to_prop_solver                    active
% 7.20/1.50  --res_prop_simpl_new                    false
% 7.20/1.50  --res_prop_simpl_given                  true
% 7.20/1.50  --res_passive_queue_type                priority_queues
% 7.20/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.20/1.50  --res_passive_queues_freq               [15;5]
% 7.20/1.50  --res_forward_subs                      full
% 7.20/1.50  --res_backward_subs                     full
% 7.20/1.50  --res_forward_subs_resolution           true
% 7.20/1.50  --res_backward_subs_resolution          true
% 7.20/1.50  --res_orphan_elimination                true
% 7.20/1.50  --res_time_limit                        2.
% 7.20/1.50  --res_out_proof                         true
% 7.20/1.50  
% 7.20/1.50  ------ Superposition Options
% 7.20/1.50  
% 7.20/1.50  --superposition_flag                    true
% 7.20/1.50  --sup_passive_queue_type                priority_queues
% 7.20/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.20/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.20/1.50  --demod_completeness_check              fast
% 7.20/1.50  --demod_use_ground                      true
% 7.20/1.50  --sup_to_prop_solver                    passive
% 7.20/1.50  --sup_prop_simpl_new                    true
% 7.20/1.50  --sup_prop_simpl_given                  true
% 7.20/1.50  --sup_fun_splitting                     false
% 7.20/1.50  --sup_smt_interval                      50000
% 7.20/1.50  
% 7.20/1.50  ------ Superposition Simplification Setup
% 7.20/1.50  
% 7.20/1.50  --sup_indices_passive                   []
% 7.20/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.20/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.20/1.50  --sup_full_bw                           [BwDemod]
% 7.20/1.50  --sup_immed_triv                        [TrivRules]
% 7.20/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.20/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.20/1.50  --sup_immed_bw_main                     []
% 7.20/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.20/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.20/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.20/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.20/1.50  
% 7.20/1.50  ------ Combination Options
% 7.20/1.50  
% 7.20/1.50  --comb_res_mult                         3
% 7.20/1.50  --comb_sup_mult                         2
% 7.20/1.50  --comb_inst_mult                        10
% 7.20/1.50  
% 7.20/1.50  ------ Debug Options
% 7.20/1.50  
% 7.20/1.50  --dbg_backtrace                         false
% 7.20/1.50  --dbg_dump_prop_clauses                 false
% 7.20/1.50  --dbg_dump_prop_clauses_file            -
% 7.20/1.50  --dbg_out_stat                          false
% 7.20/1.50  
% 7.20/1.50  
% 7.20/1.50  
% 7.20/1.50  
% 7.20/1.50  ------ Proving...
% 7.20/1.50  
% 7.20/1.50  
% 7.20/1.50  % SZS status Theorem for theBenchmark.p
% 7.20/1.50  
% 7.20/1.50   Resolution empty clause
% 7.20/1.50  
% 7.20/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.20/1.50  
% 7.20/1.50  fof(f15,conjecture,(
% 7.20/1.50    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f16,negated_conjecture,(
% 7.20/1.50    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 7.20/1.50    inference(negated_conjecture,[],[f15])).
% 7.20/1.50  
% 7.20/1.50  fof(f26,plain,(
% 7.20/1.50    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 7.20/1.50    inference(ennf_transformation,[],[f16])).
% 7.20/1.50  
% 7.20/1.50  fof(f27,plain,(
% 7.20/1.50    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 7.20/1.50    inference(flattening,[],[f26])).
% 7.20/1.50  
% 7.20/1.50  fof(f36,plain,(
% 7.20/1.50    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 7.20/1.50    introduced(choice_axiom,[])).
% 7.20/1.50  
% 7.20/1.50  fof(f37,plain,(
% 7.20/1.50    k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 7.20/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f27,f36])).
% 7.20/1.50  
% 7.20/1.50  fof(f62,plain,(
% 7.20/1.50    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 7.20/1.50    inference(cnf_transformation,[],[f37])).
% 7.20/1.50  
% 7.20/1.50  fof(f7,axiom,(
% 7.20/1.50    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f45,plain,(
% 7.20/1.50    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f7])).
% 7.20/1.50  
% 7.20/1.50  fof(f78,plain,(
% 7.20/1.50    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 7.20/1.50    inference(definition_unfolding,[],[f62,f45])).
% 7.20/1.50  
% 7.20/1.50  fof(f5,axiom,(
% 7.20/1.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f20,plain,(
% 7.20/1.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.20/1.50    inference(ennf_transformation,[],[f5])).
% 7.20/1.50  
% 7.20/1.50  fof(f21,plain,(
% 7.20/1.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.20/1.50    inference(flattening,[],[f20])).
% 7.20/1.50  
% 7.20/1.50  fof(f43,plain,(
% 7.20/1.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f21])).
% 7.20/1.50  
% 7.20/1.50  fof(f3,axiom,(
% 7.20/1.50    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f18,plain,(
% 7.20/1.50    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.20/1.50    inference(ennf_transformation,[],[f3])).
% 7.20/1.50  
% 7.20/1.50  fof(f32,plain,(
% 7.20/1.50    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK1(X0),sK2(X0)) = X0)),
% 7.20/1.50    introduced(choice_axiom,[])).
% 7.20/1.50  
% 7.20/1.50  fof(f33,plain,(
% 7.20/1.50    ! [X0,X1,X2] : (k4_tarski(sK1(X0),sK2(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.20/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f32])).
% 7.20/1.50  
% 7.20/1.50  fof(f41,plain,(
% 7.20/1.50    ( ! [X2,X0,X1] : (k4_tarski(sK1(X0),sK2(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 7.20/1.50    inference(cnf_transformation,[],[f33])).
% 7.20/1.50  
% 7.20/1.50  fof(f2,axiom,(
% 7.20/1.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f17,plain,(
% 7.20/1.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.20/1.50    inference(ennf_transformation,[],[f2])).
% 7.20/1.50  
% 7.20/1.50  fof(f40,plain,(
% 7.20/1.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f17])).
% 7.20/1.50  
% 7.20/1.50  fof(f13,axiom,(
% 7.20/1.50    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f34,plain,(
% 7.20/1.50    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 7.20/1.50    inference(nnf_transformation,[],[f13])).
% 7.20/1.50  
% 7.20/1.50  fof(f35,plain,(
% 7.20/1.50    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.20/1.50    inference(flattening,[],[f34])).
% 7.20/1.50  
% 7.20/1.50  fof(f57,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f35])).
% 7.20/1.50  
% 7.20/1.50  fof(f8,axiom,(
% 7.20/1.50    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f46,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f8])).
% 7.20/1.50  
% 7.20/1.50  fof(f68,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 7.20/1.50    inference(definition_unfolding,[],[f46,f45])).
% 7.20/1.50  
% 7.20/1.50  fof(f74,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 7.20/1.50    inference(definition_unfolding,[],[f57,f68])).
% 7.20/1.50  
% 7.20/1.50  fof(f83,plain,(
% 7.20/1.50    ( ! [X2,X0,X3] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3)) )),
% 7.20/1.50    inference(equality_resolution,[],[f74])).
% 7.20/1.50  
% 7.20/1.50  fof(f11,axiom,(
% 7.20/1.50    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f24,plain,(
% 7.20/1.50    ! [X0,X1] : (! [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 7.20/1.50    inference(ennf_transformation,[],[f11])).
% 7.20/1.50  
% 7.20/1.50  fof(f51,plain,(
% 7.20/1.50    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.20/1.50    inference(cnf_transformation,[],[f24])).
% 7.20/1.50  
% 7.20/1.50  fof(f9,axiom,(
% 7.20/1.50    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f22,plain,(
% 7.20/1.50    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.20/1.50    inference(ennf_transformation,[],[f9])).
% 7.20/1.50  
% 7.20/1.50  fof(f47,plain,(
% 7.20/1.50    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 7.20/1.50    inference(cnf_transformation,[],[f22])).
% 7.20/1.50  
% 7.20/1.50  fof(f64,plain,(
% 7.20/1.50    k1_xboole_0 != sK3),
% 7.20/1.50    inference(cnf_transformation,[],[f37])).
% 7.20/1.50  
% 7.20/1.50  fof(f65,plain,(
% 7.20/1.50    k1_xboole_0 != sK4),
% 7.20/1.50    inference(cnf_transformation,[],[f37])).
% 7.20/1.50  
% 7.20/1.50  fof(f66,plain,(
% 7.20/1.50    k1_xboole_0 != sK5),
% 7.20/1.50    inference(cnf_transformation,[],[f37])).
% 7.20/1.50  
% 7.20/1.50  fof(f55,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.20/1.50    inference(cnf_transformation,[],[f35])).
% 7.20/1.50  
% 7.20/1.50  fof(f76,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.20/1.50    inference(definition_unfolding,[],[f55,f68])).
% 7.20/1.50  
% 7.20/1.50  fof(f56,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f35])).
% 7.20/1.50  
% 7.20/1.50  fof(f75,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 7.20/1.50    inference(definition_unfolding,[],[f56,f68])).
% 7.20/1.50  
% 7.20/1.50  fof(f84,plain,(
% 7.20/1.50    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 7.20/1.50    inference(equality_resolution,[],[f75])).
% 7.20/1.50  
% 7.20/1.50  fof(f58,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f35])).
% 7.20/1.50  
% 7.20/1.50  fof(f73,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 7.20/1.50    inference(definition_unfolding,[],[f58,f68])).
% 7.20/1.50  
% 7.20/1.50  fof(f82,plain,(
% 7.20/1.50    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 7.20/1.50    inference(equality_resolution,[],[f73])).
% 7.20/1.50  
% 7.20/1.50  fof(f10,axiom,(
% 7.20/1.50    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f23,plain,(
% 7.20/1.50    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 7.20/1.50    inference(ennf_transformation,[],[f10])).
% 7.20/1.50  
% 7.20/1.50  fof(f50,plain,(
% 7.20/1.50    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 7.20/1.50    inference(cnf_transformation,[],[f23])).
% 7.20/1.50  
% 7.20/1.50  fof(f79,plain,(
% 7.20/1.50    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 7.20/1.50    inference(equality_resolution,[],[f50])).
% 7.20/1.50  
% 7.20/1.50  fof(f14,axiom,(
% 7.20/1.50    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f61,plain,(
% 7.20/1.50    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 7.20/1.50    inference(cnf_transformation,[],[f14])).
% 7.20/1.50  
% 7.20/1.50  fof(f60,plain,(
% 7.20/1.50    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 7.20/1.50    inference(cnf_transformation,[],[f14])).
% 7.20/1.50  
% 7.20/1.50  fof(f1,axiom,(
% 7.20/1.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f28,plain,(
% 7.20/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.20/1.50    inference(nnf_transformation,[],[f1])).
% 7.20/1.50  
% 7.20/1.50  fof(f29,plain,(
% 7.20/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.20/1.50    inference(rectify,[],[f28])).
% 7.20/1.50  
% 7.20/1.50  fof(f30,plain,(
% 7.20/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.20/1.50    introduced(choice_axiom,[])).
% 7.20/1.50  
% 7.20/1.50  fof(f31,plain,(
% 7.20/1.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.20/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 7.20/1.50  
% 7.20/1.50  fof(f39,plain,(
% 7.20/1.50    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f31])).
% 7.20/1.50  
% 7.20/1.50  fof(f38,plain,(
% 7.20/1.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f31])).
% 7.20/1.50  
% 7.20/1.50  fof(f63,plain,(
% 7.20/1.50    ( ! [X6,X7,X5] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f37])).
% 7.20/1.50  
% 7.20/1.50  fof(f6,axiom,(
% 7.20/1.50    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f44,plain,(
% 7.20/1.50    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f6])).
% 7.20/1.50  
% 7.20/1.50  fof(f77,plain,(
% 7.20/1.50    ( ! [X6,X7,X5] : (sK6 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 7.20/1.50    inference(definition_unfolding,[],[f63,f44])).
% 7.20/1.50  
% 7.20/1.50  fof(f48,plain,(
% 7.20/1.50    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 7.20/1.50    inference(cnf_transformation,[],[f22])).
% 7.20/1.50  
% 7.20/1.50  fof(f4,axiom,(
% 7.20/1.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f19,plain,(
% 7.20/1.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.20/1.50    inference(ennf_transformation,[],[f4])).
% 7.20/1.50  
% 7.20/1.50  fof(f42,plain,(
% 7.20/1.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.20/1.50    inference(cnf_transformation,[],[f19])).
% 7.20/1.50  
% 7.20/1.50  fof(f12,axiom,(
% 7.20/1.50    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.20/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.20/1.50  
% 7.20/1.50  fof(f25,plain,(
% 7.20/1.50    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 7.20/1.50    inference(ennf_transformation,[],[f12])).
% 7.20/1.50  
% 7.20/1.50  fof(f54,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.20/1.50    inference(cnf_transformation,[],[f25])).
% 7.20/1.50  
% 7.20/1.50  fof(f69,plain,(
% 7.20/1.50    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.20/1.50    inference(definition_unfolding,[],[f54,f45])).
% 7.20/1.50  
% 7.20/1.50  fof(f67,plain,(
% 7.20/1.50    k7_mcart_1(sK3,sK4,sK5,sK7) != sK6),
% 7.20/1.50    inference(cnf_transformation,[],[f37])).
% 7.20/1.50  
% 7.20/1.50  cnf(c_26,negated_conjecture,
% 7.20/1.50      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 7.20/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_503,plain,
% 7.20/1.50      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_5,plain,
% 7.20/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.20/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_511,plain,
% 7.20/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.20/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.20/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3510,plain,
% 7.20/1.50      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_503,c_511]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3,plain,
% 7.20/1.50      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
% 7.20/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_513,plain,
% 7.20/1.50      ( k4_tarski(sK1(X0),sK2(X0)) = X0
% 7.20/1.50      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3743,plain,
% 7.20/1.50      ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3510,c_513]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2,plain,
% 7.20/1.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.20/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_514,plain,
% 7.20/1.50      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3801,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 7.20/1.50      | k4_tarski(sK1(sK7),sK2(sK7)) = sK7 ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3743,c_514]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_4659,plain,
% 7.20/1.50      ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7
% 7.20/1.50      | m1_subset_1(sK7,k1_xboole_0) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3801,c_503]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_16,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1),X2) = k1_xboole_0 ),
% 7.20/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_10,plain,
% 7.20/1.50      ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
% 7.20/1.50      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | k1_xboole_0 = X2 ),
% 7.20/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_508,plain,
% 7.20/1.50      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | k1_xboole_0 = X2
% 7.20/1.50      | m1_subset_1(X0,k2_zfmisc_1(X2,X1)) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3461,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0
% 7.20/1.50      | k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
% 7.20/1.50      | k1_xboole_0 = X3
% 7.20/1.50      | m1_subset_1(X2,k1_xboole_0) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_16,c_508]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_5086,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0
% 7.20/1.50      | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
% 7.20/1.50      | k4_tarski(sK1(sK7),sK2(sK7)) = sK7
% 7.20/1.50      | k1_xboole_0 = X2 ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_4659,c_3461]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_7,plain,
% 7.20/1.50      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 7.20/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_509,plain,
% 7.20/1.50      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.20/1.50      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_5288,plain,
% 7.20/1.50      ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
% 7.20/1.50      | k4_tarski(sK1(sK7),sK2(sK7)) = sK7
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 7.20/1.50      | r2_hidden(k1_mcart_1(X1),k2_zfmisc_1(X2,k1_xboole_0)) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_5086,c_509]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_24,negated_conjecture,
% 7.20/1.50      ( k1_xboole_0 != sK3 ),
% 7.20/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_23,negated_conjecture,
% 7.20/1.50      ( k1_xboole_0 != sK4 ),
% 7.20/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_22,negated_conjecture,
% 7.20/1.50      ( k1_xboole_0 != sK5 ),
% 7.20/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_18,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | k1_xboole_0 = X2
% 7.20/1.50      | k1_xboole_0 = X3 ),
% 7.20/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_33,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_17,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 7.20/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_34,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_17]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_250,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_685,plain,
% 7.20/1.50      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_250]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_686,plain,
% 7.20/1.50      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_685]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_687,plain,
% 7.20/1.50      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_250]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_688,plain,
% 7.20/1.50      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_687]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_689,plain,
% 7.20/1.50      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_250]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_690,plain,
% 7.20/1.50      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_689]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_4651,plain,
% 7.20/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 7.20/1.50      | k4_tarski(sK1(sK7),sK2(sK7)) = sK7
% 7.20/1.50      | sK5 = k1_xboole_0
% 7.20/1.50      | sK4 = k1_xboole_0
% 7.20/1.50      | sK3 = k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0 ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3801,c_18]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_15,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
% 7.20/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_996,plain,
% 7.20/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_15,c_15]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_4700,plain,
% 7.20/1.50      ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7
% 7.20/1.50      | sK5 = k1_xboole_0
% 7.20/1.50      | sK4 = k1_xboole_0
% 7.20/1.50      | sK3 = k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.20/1.50      inference(light_normalisation,[status(thm)],[c_4651,c_996]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_4701,plain,
% 7.20/1.50      ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7
% 7.20/1.50      | sK5 = k1_xboole_0
% 7.20/1.50      | sK4 = k1_xboole_0
% 7.20/1.50      | sK3 = k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0 ),
% 7.20/1.50      inference(equality_resolution_simp,[status(thm)],[c_4700]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_7064,plain,
% 7.20/1.50      ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7 | k1_xboole_0 = X0 ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_5288,c_24,c_23,c_22,c_33,c_34,c_686,c_688,c_690,c_4701]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_8,plain,
% 7.20/1.50      ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
% 7.20/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_19,plain,
% 7.20/1.50      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 7.20/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_542,plain,
% 7.20/1.50      ( k4_tarski(X0,X1) != X1 ),
% 7.20/1.50      inference(light_normalisation,[status(thm)],[c_8,c_19]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_7263,plain,
% 7.20/1.50      ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7 | k1_xboole_0 != X0 ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_7064,c_542]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_7458,plain,
% 7.20/1.50      ( k4_tarski(sK1(sK7),sK2(sK7)) = sK7 ),
% 7.20/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_7263,c_7064]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_20,plain,
% 7.20/1.50      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 7.20/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_7485,plain,
% 7.20/1.50      ( k1_mcart_1(sK7) = sK1(sK7) ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_7458,c_20]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3745,plain,
% 7.20/1.50      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) = iProver_top
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3510,c_509]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3816,plain,
% 7.20/1.50      ( k4_tarski(sK1(k1_mcart_1(sK7)),sK2(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3745,c_513]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_8464,plain,
% 7.20/1.50      ( k4_tarski(sK1(sK1(sK7)),sK2(sK1(sK7))) = sK1(sK7)
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(demodulation,[status(thm)],[c_7485,c_3816]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_0,plain,
% 7.20/1.50      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.20/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_516,plain,
% 7.20/1.50      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2614,plain,
% 7.20/1.50      ( r2_hidden(k1_mcart_1(sK0(k2_zfmisc_1(X0,X1))),X0) = iProver_top
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_516,c_509]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1,plain,
% 7.20/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.20/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_515,plain,
% 7.20/1.50      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_12508,plain,
% 7.20/1.50      ( v1_xboole_0(X0) != iProver_top
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_2614,c_515]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_12668,plain,
% 7.20/1.50      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_12508,c_514]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_17246,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) = k1_xboole_0
% 7.20/1.50      | k4_tarski(sK1(sK1(sK7)),sK2(sK1(sK7))) = sK1(sK7) ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_8464,c_12668]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_24388,plain,
% 7.20/1.50      ( k4_tarski(sK1(sK1(sK7)),sK2(sK1(sK7))) = sK1(sK7)
% 7.20/1.50      | sK5 = k1_xboole_0
% 7.20/1.50      | sK4 = k1_xboole_0
% 7.20/1.50      | sK3 = k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0 ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_17246,c_18]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_25805,plain,
% 7.20/1.50      ( k4_tarski(sK1(sK1(sK7)),sK2(sK1(sK7))) = sK1(sK7) | k1_xboole_0 = X0 ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_24388,c_24,c_23,c_22,c_33,c_34,c_686,c_688,c_690]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_25,negated_conjecture,
% 7.20/1.50      ( ~ m1_subset_1(X0,sK5)
% 7.20/1.50      | ~ m1_subset_1(X1,sK4)
% 7.20/1.50      | ~ m1_subset_1(X2,sK3)
% 7.20/1.50      | k4_tarski(k4_tarski(X2,X1),X0) != sK7
% 7.20/1.50      | sK6 = X0 ),
% 7.20/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_504,plain,
% 7.20/1.50      ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
% 7.20/1.50      | sK6 = X2
% 7.20/1.50      | m1_subset_1(X2,sK5) != iProver_top
% 7.20/1.50      | m1_subset_1(X1,sK4) != iProver_top
% 7.20/1.50      | m1_subset_1(X0,sK3) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_26314,plain,
% 7.20/1.50      ( k4_tarski(sK1(sK7),X0) != sK7
% 7.20/1.50      | sK6 = X0
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | m1_subset_1(X0,sK5) != iProver_top
% 7.20/1.50      | m1_subset_1(sK2(sK1(sK7)),sK4) != iProver_top
% 7.20/1.50      | m1_subset_1(sK1(sK1(sK7)),sK3) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_25805,c_504]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_6183,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 7.20/1.50      | k4_tarski(sK1(k1_mcart_1(sK7)),sK2(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3816,c_514]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_13432,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 7.20/1.50      | k4_tarski(sK1(sK1(sK7)),sK2(sK1(sK7))) = sK1(sK7) ),
% 7.20/1.50      inference(light_normalisation,[status(thm)],[c_6183,c_7485]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_13441,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 7.20/1.50      | k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7)) ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_13432,c_20]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_13877,plain,
% 7.20/1.50      ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
% 7.20/1.50      | m1_subset_1(sK7,k1_xboole_0) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_13441,c_503]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_14751,plain,
% 7.20/1.50      ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
% 7.20/1.50      | r2_hidden(sK7,k1_xboole_0) = iProver_top
% 7.20/1.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_13877,c_511]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_6,plain,
% 7.20/1.50      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2) ),
% 7.20/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_510,plain,
% 7.20/1.50      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.20/1.50      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_2998,plain,
% 7.20/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.20/1.50      | r2_hidden(k2_mcart_1(X0),X1) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_15,c_510]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_4,plain,
% 7.20/1.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.20/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_512,plain,
% 7.20/1.50      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3170,plain,
% 7.20/1.50      ( m1_subset_1(k2_mcart_1(X0),X1) = iProver_top
% 7.20/1.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_2998,c_512]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_11,plain,
% 7.20/1.50      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.20/1.50      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | k1_xboole_0 = X2
% 7.20/1.50      | k1_xboole_0 = X3 ),
% 7.20/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_507,plain,
% 7.20/1.50      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 = X2
% 7.20/1.50      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 7.20/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3301,plain,
% 7.20/1.50      ( k7_mcart_1(X0,X1,X2,k2_mcart_1(X3)) = k2_mcart_1(k2_mcart_1(X3))
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 = X2
% 7.20/1.50      | r2_hidden(X3,k1_xboole_0) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3170,c_507]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_19066,plain,
% 7.20/1.50      ( k7_mcart_1(X0,X1,X2,k2_mcart_1(sK7)) = k2_mcart_1(k2_mcart_1(sK7))
% 7.20/1.50      | k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 = X2
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_14751,c_3301]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_7486,plain,
% 7.20/1.50      ( k2_mcart_1(sK7) = sK2(sK7) ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_7458,c_19]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_19145,plain,
% 7.20/1.50      ( k7_mcart_1(X0,X1,X2,sK2(sK7)) = k2_mcart_1(sK2(sK7))
% 7.20/1.50      | k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 = X2
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.20/1.50      inference(light_normalisation,[status(thm)],[c_19066,c_7486]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_13868,plain,
% 7.20/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 7.20/1.50      | k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
% 7.20/1.50      | sK5 = k1_xboole_0
% 7.20/1.50      | sK4 = k1_xboole_0
% 7.20/1.50      | sK3 = k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0 ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_13441,c_18]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_13922,plain,
% 7.20/1.50      ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
% 7.20/1.50      | sK5 = k1_xboole_0
% 7.20/1.50      | sK4 = k1_xboole_0
% 7.20/1.50      | sK3 = k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.20/1.50      inference(light_normalisation,[status(thm)],[c_13868,c_996]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_13923,plain,
% 7.20/1.50      ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7))
% 7.20/1.50      | sK5 = k1_xboole_0
% 7.20/1.50      | sK4 = k1_xboole_0
% 7.20/1.50      | sK3 = k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0 ),
% 7.20/1.50      inference(equality_resolution_simp,[status(thm)],[c_13922]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_19826,plain,
% 7.20/1.50      ( k1_xboole_0 = X0 | k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7)) ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_19145,c_24,c_23,c_22,c_33,c_34,c_686,c_688,c_690,c_13923]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_19827,plain,
% 7.20/1.50      ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7)) | k1_xboole_0 = X0 ),
% 7.20/1.50      inference(renaming,[status(thm)],[c_19826]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3818,plain,
% 7.20/1.50      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3745,c_509]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_6137,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 7.20/1.50      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3818,c_514]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_11601,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 7.20/1.50      | r2_hidden(k1_mcart_1(sK1(sK7)),sK3) = iProver_top ),
% 7.20/1.50      inference(light_normalisation,[status(thm)],[c_6137,c_7485]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_20225,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | r2_hidden(sK1(sK1(sK7)),sK3) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_19827,c_11601]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_702,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,X0),X1),X2) != k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 = X2
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | k1_xboole_0 = sK3 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_899,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),X0),X1) != k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | k1_xboole_0 = sK4
% 7.20/1.50      | k1_xboole_0 = sK3 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_702]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_1378,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) != k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 = sK5
% 7.20/1.50      | k1_xboole_0 = sK4
% 7.20/1.50      | k1_xboole_0 = sK3 ),
% 7.20/1.50      inference(instantiation,[status(thm)],[c_899]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_20197,plain,
% 7.20/1.50      ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7)) | k1_xboole_0 != X0 ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_19827,c_542]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_20360,plain,
% 7.20/1.50      ( k1_mcart_1(sK1(sK7)) = sK1(sK1(sK7)) ),
% 7.20/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_20197,c_19827]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_8466,plain,
% 7.20/1.50      ( r2_hidden(k1_mcart_1(sK1(sK7)),sK3) = iProver_top
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(demodulation,[status(thm)],[c_7485,c_3818]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_20943,plain,
% 7.20/1.50      ( r2_hidden(sK1(sK1(sK7)),sK3) = iProver_top
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(demodulation,[status(thm)],[c_20360,c_8466]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_21762,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) = k1_xboole_0
% 7.20/1.50      | r2_hidden(sK1(sK1(sK7)),sK3) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_20943,c_12668]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_23198,plain,
% 7.20/1.50      ( k1_xboole_0 = X0 | r2_hidden(sK1(sK1(sK7)),sK3) = iProver_top ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_20225,c_24,c_23,c_22,c_1378,c_21762]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_23205,plain,
% 7.20/1.50      ( k1_xboole_0 = X0 | m1_subset_1(sK1(sK1(sK7)),sK3) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_23198,c_512]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_13442,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 7.20/1.50      | k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7)) ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_13432,c_19]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_14090,plain,
% 7.20/1.50      ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
% 7.20/1.50      | m1_subset_1(sK7,k1_xboole_0) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_13442,c_503]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_14846,plain,
% 7.20/1.50      ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
% 7.20/1.50      | r2_hidden(sK7,k1_xboole_0) = iProver_top
% 7.20/1.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_14090,c_511]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_19065,plain,
% 7.20/1.50      ( k7_mcart_1(X0,X1,X2,k2_mcart_1(sK7)) = k2_mcart_1(k2_mcart_1(sK7))
% 7.20/1.50      | k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 = X2
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_14846,c_3301]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_19158,plain,
% 7.20/1.50      ( k7_mcart_1(X0,X1,X2,sK2(sK7)) = k2_mcart_1(sK2(sK7))
% 7.20/1.50      | k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 = X2
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.20/1.50      inference(light_normalisation,[status(thm)],[c_19065,c_7486]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_14081,plain,
% 7.20/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 7.20/1.50      | k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
% 7.20/1.50      | sK5 = k1_xboole_0
% 7.20/1.50      | sK4 = k1_xboole_0
% 7.20/1.50      | sK3 = k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0 ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_13442,c_18]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_14135,plain,
% 7.20/1.50      ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
% 7.20/1.50      | sK5 = k1_xboole_0
% 7.20/1.50      | sK4 = k1_xboole_0
% 7.20/1.50      | sK3 = k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.20/1.50      inference(light_normalisation,[status(thm)],[c_14081,c_996]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_14136,plain,
% 7.20/1.50      ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7))
% 7.20/1.50      | sK5 = k1_xboole_0
% 7.20/1.50      | sK4 = k1_xboole_0
% 7.20/1.50      | sK3 = k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0 ),
% 7.20/1.50      inference(equality_resolution_simp,[status(thm)],[c_14135]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_20373,plain,
% 7.20/1.50      ( k1_xboole_0 = X0 | k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7)) ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_19158,c_24,c_23,c_22,c_33,c_34,c_686,c_688,c_690,c_14136]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_20374,plain,
% 7.20/1.50      ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7)) | k1_xboole_0 = X0 ),
% 7.20/1.50      inference(renaming,[status(thm)],[c_20373]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3817,plain,
% 7.20/1.50      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3745,c_510]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_6121,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 7.20/1.50      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3817,c_514]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_11584,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 7.20/1.50      | r2_hidden(k2_mcart_1(sK1(sK7)),sK4) = iProver_top ),
% 7.20/1.50      inference(light_normalisation,[status(thm)],[c_6121,c_7485]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_20765,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | r2_hidden(sK2(sK1(sK7)),sK4) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_20374,c_11584]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_20735,plain,
% 7.20/1.50      ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7)) | k1_xboole_0 != X0 ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_20374,c_542]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_20912,plain,
% 7.20/1.50      ( k2_mcart_1(sK1(sK7)) = sK2(sK1(sK7)) ),
% 7.20/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_20735,c_20374]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_8467,plain,
% 7.20/1.50      ( r2_hidden(k2_mcart_1(sK1(sK7)),sK4) = iProver_top
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(demodulation,[status(thm)],[c_7485,c_3817]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_21020,plain,
% 7.20/1.50      ( r2_hidden(sK2(sK1(sK7)),sK4) = iProver_top
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(demodulation,[status(thm)],[c_20912,c_8467]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_21786,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) = k1_xboole_0
% 7.20/1.50      | r2_hidden(sK2(sK1(sK7)),sK4) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_21020,c_12668]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_24277,plain,
% 7.20/1.50      ( k1_xboole_0 = X0 | r2_hidden(sK2(sK1(sK7)),sK4) = iProver_top ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_20765,c_24,c_23,c_22,c_1378,c_21786]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_24284,plain,
% 7.20/1.50      ( k1_xboole_0 = X0 | m1_subset_1(sK2(sK1(sK7)),sK4) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_24277,c_512]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_26481,plain,
% 7.20/1.50      ( k4_tarski(sK1(sK7),X0) != sK7
% 7.20/1.50      | sK6 = X0
% 7.20/1.50      | k1_xboole_0 = X1
% 7.20/1.50      | m1_subset_1(X0,sK5) != iProver_top ),
% 7.20/1.50      inference(forward_subsumption_resolution,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_26314,c_23205,c_24284]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_26483,plain,
% 7.20/1.50      ( sK2(sK7) = sK6
% 7.20/1.50      | k1_xboole_0 = X0
% 7.20/1.50      | m1_subset_1(sK2(sK7),sK5) != iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_7458,c_26481]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3026,plain,
% 7.20/1.50      ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7)
% 7.20/1.50      | sK5 = k1_xboole_0
% 7.20/1.50      | sK4 = k1_xboole_0
% 7.20/1.50      | sK3 = k1_xboole_0 ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_503,c_507]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3275,plain,
% 7.20/1.50      ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7) ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_3026,c_24,c_23,c_22,c_33,c_34,c_686,c_688,c_690]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_21,negated_conjecture,
% 7.20/1.50      ( k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
% 7.20/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3278,plain,
% 7.20/1.50      ( k2_mcart_1(sK7) != sK6 ),
% 7.20/1.50      inference(demodulation,[status(thm)],[c_3275,c_21]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_8523,plain,
% 7.20/1.50      ( sK2(sK7) != sK6 ),
% 7.20/1.50      inference(demodulation,[status(thm)],[c_7486,c_3278]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_3744,plain,
% 7.20/1.50      ( r2_hidden(k2_mcart_1(sK7),sK5) = iProver_top
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_3510,c_510]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_8521,plain,
% 7.20/1.50      ( r2_hidden(sK2(sK7),sK5) = iProver_top
% 7.20/1.50      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 7.20/1.50      inference(demodulation,[status(thm)],[c_7486,c_3744]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_13267,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) = k1_xboole_0
% 7.20/1.50      | r2_hidden(sK2(sK7),sK5) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_8521,c_12668]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_13402,plain,
% 7.20/1.50      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) = k1_xboole_0
% 7.20/1.50      | m1_subset_1(sK2(sK7),sK5) = iProver_top ),
% 7.20/1.50      inference(superposition,[status(thm)],[c_13267,c_512]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_26490,plain,
% 7.20/1.50      ( k1_xboole_0 = X0 ),
% 7.20/1.50      inference(global_propositional_subsumption,
% 7.20/1.50                [status(thm)],
% 7.20/1.50                [c_26483,c_24,c_23,c_22,c_1378,c_8523,c_13402]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_26595,plain,
% 7.20/1.50      ( k1_xboole_0 != k1_xboole_0 ),
% 7.20/1.50      inference(demodulation,[status(thm)],[c_26490,c_22]) ).
% 7.20/1.50  
% 7.20/1.50  cnf(c_26898,plain,
% 7.20/1.50      ( $false ),
% 7.20/1.50      inference(equality_resolution_simp,[status(thm)],[c_26595]) ).
% 7.20/1.50  
% 7.20/1.50  
% 7.20/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.20/1.50  
% 7.20/1.50  ------                               Statistics
% 7.20/1.50  
% 7.20/1.50  ------ General
% 7.20/1.50  
% 7.20/1.50  abstr_ref_over_cycles:                  0
% 7.20/1.50  abstr_ref_under_cycles:                 0
% 7.20/1.50  gc_basic_clause_elim:                   0
% 7.20/1.50  forced_gc_time:                         0
% 7.20/1.50  parsing_time:                           0.023
% 7.20/1.50  unif_index_cands_time:                  0.
% 7.20/1.50  unif_index_add_time:                    0.
% 7.20/1.50  orderings_time:                         0.
% 7.20/1.50  out_proof_time:                         0.013
% 7.20/1.50  total_time:                             0.611
% 7.20/1.50  num_of_symbols:                         50
% 7.20/1.50  num_of_terms:                           21862
% 7.20/1.50  
% 7.20/1.50  ------ Preprocessing
% 7.20/1.50  
% 7.20/1.50  num_of_splits:                          0
% 7.20/1.50  num_of_split_atoms:                     0
% 7.20/1.50  num_of_reused_defs:                     0
% 7.20/1.50  num_eq_ax_congr_red:                    24
% 7.20/1.50  num_of_sem_filtered_clauses:            1
% 7.20/1.50  num_of_subtypes:                        0
% 7.20/1.50  monotx_restored_types:                  0
% 7.20/1.50  sat_num_of_epr_types:                   0
% 7.20/1.50  sat_num_of_non_cyclic_types:            0
% 7.20/1.50  sat_guarded_non_collapsed_types:        0
% 7.20/1.50  num_pure_diseq_elim:                    0
% 7.20/1.50  simp_replaced_by:                       0
% 7.20/1.50  res_preprocessed:                       100
% 7.20/1.50  prep_upred:                             0
% 7.20/1.50  prep_unflattend:                        2
% 7.20/1.50  smt_new_axioms:                         0
% 7.20/1.50  pred_elim_cands:                        3
% 7.20/1.50  pred_elim:                              0
% 7.20/1.50  pred_elim_cl:                           0
% 7.20/1.50  pred_elim_cycles:                       1
% 7.20/1.50  merged_defs:                            0
% 7.20/1.50  merged_defs_ncl:                        0
% 7.20/1.50  bin_hyper_res:                          0
% 7.20/1.50  prep_cycles:                            3
% 7.20/1.50  pred_elim_time:                         0.001
% 7.20/1.50  splitting_time:                         0.
% 7.20/1.50  sem_filter_time:                        0.
% 7.20/1.50  monotx_time:                            0.001
% 7.20/1.50  subtype_inf_time:                       0.
% 7.20/1.50  
% 7.20/1.50  ------ Problem properties
% 7.20/1.50  
% 7.20/1.50  clauses:                                27
% 7.20/1.50  conjectures:                            6
% 7.20/1.50  epr:                                    7
% 7.20/1.50  horn:                                   20
% 7.20/1.50  ground:                                 5
% 7.20/1.50  unary:                                  13
% 7.20/1.50  binary:                                 7
% 7.20/1.50  lits:                                   59
% 7.20/1.50  lits_eq:                                36
% 7.20/1.50  fd_pure:                                0
% 7.20/1.50  fd_pseudo:                              0
% 7.20/1.50  fd_cond:                                6
% 7.20/1.50  fd_pseudo_cond:                         0
% 7.20/1.50  ac_symbols:                             0
% 7.20/1.50  
% 7.20/1.50  ------ Propositional Solver
% 7.20/1.50  
% 7.20/1.50  prop_solver_calls:                      25
% 7.20/1.50  prop_fast_solver_calls:                 1355
% 7.20/1.50  smt_solver_calls:                       0
% 7.20/1.50  smt_fast_solver_calls:                  0
% 7.20/1.50  prop_num_of_clauses:                    7918
% 7.20/1.50  prop_preprocess_simplified:             15770
% 7.20/1.50  prop_fo_subsumed:                       113
% 7.20/1.50  prop_solver_time:                       0.
% 7.20/1.50  smt_solver_time:                        0.
% 7.20/1.50  smt_fast_solver_time:                   0.
% 7.20/1.50  prop_fast_solver_time:                  0.
% 7.20/1.50  prop_unsat_core_time:                   0.
% 7.20/1.50  
% 7.20/1.50  ------ QBF
% 7.20/1.50  
% 7.20/1.50  qbf_q_res:                              0
% 7.20/1.50  qbf_num_tautologies:                    0
% 7.20/1.50  qbf_prep_cycles:                        0
% 7.20/1.50  
% 7.20/1.50  ------ BMC1
% 7.20/1.50  
% 7.20/1.50  bmc1_current_bound:                     -1
% 7.20/1.50  bmc1_last_solved_bound:                 -1
% 7.20/1.50  bmc1_unsat_core_size:                   -1
% 7.20/1.50  bmc1_unsat_core_parents_size:           -1
% 7.20/1.50  bmc1_merge_next_fun:                    0
% 7.20/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.20/1.50  
% 7.20/1.50  ------ Instantiation
% 7.20/1.50  
% 7.20/1.50  inst_num_of_clauses:                    2671
% 7.20/1.50  inst_num_in_passive:                    238
% 7.20/1.50  inst_num_in_active:                     1209
% 7.20/1.50  inst_num_in_unprocessed:                1224
% 7.20/1.50  inst_num_of_loops:                      1220
% 7.20/1.50  inst_num_of_learning_restarts:          0
% 7.20/1.50  inst_num_moves_active_passive:          10
% 7.20/1.50  inst_lit_activity:                      0
% 7.20/1.50  inst_lit_activity_moves:                0
% 7.20/1.50  inst_num_tautologies:                   0
% 7.20/1.50  inst_num_prop_implied:                  0
% 7.20/1.50  inst_num_existing_simplified:           0
% 7.20/1.50  inst_num_eq_res_simplified:             0
% 7.20/1.50  inst_num_child_elim:                    0
% 7.20/1.50  inst_num_of_dismatching_blockings:      364
% 7.20/1.50  inst_num_of_non_proper_insts:           1647
% 7.20/1.50  inst_num_of_duplicates:                 0
% 7.20/1.50  inst_inst_num_from_inst_to_res:         0
% 7.20/1.50  inst_dismatching_checking_time:         0.
% 7.20/1.50  
% 7.20/1.50  ------ Resolution
% 7.20/1.50  
% 7.20/1.50  res_num_of_clauses:                     0
% 7.20/1.50  res_num_in_passive:                     0
% 7.20/1.50  res_num_in_active:                      0
% 7.20/1.50  res_num_of_loops:                       103
% 7.20/1.50  res_forward_subset_subsumed:            53
% 7.20/1.50  res_backward_subset_subsumed:           0
% 7.20/1.50  res_forward_subsumed:                   0
% 7.20/1.50  res_backward_subsumed:                  0
% 7.20/1.50  res_forward_subsumption_resolution:     0
% 7.20/1.50  res_backward_subsumption_resolution:    0
% 7.20/1.50  res_clause_to_clause_subsumption:       3009
% 7.20/1.50  res_orphan_elimination:                 0
% 7.20/1.50  res_tautology_del:                      20
% 7.20/1.50  res_num_eq_res_simplified:              0
% 7.20/1.50  res_num_sel_changes:                    0
% 7.20/1.50  res_moves_from_active_to_pass:          0
% 7.20/1.50  
% 7.20/1.50  ------ Superposition
% 7.20/1.50  
% 7.20/1.50  sup_time_total:                         0.
% 7.20/1.50  sup_time_generating:                    0.
% 7.20/1.50  sup_time_sim_full:                      0.
% 7.20/1.50  sup_time_sim_immed:                     0.
% 7.20/1.50  
% 7.20/1.50  sup_num_of_clauses:                     575
% 7.20/1.50  sup_num_in_active:                      7
% 7.20/1.50  sup_num_in_passive:                     568
% 7.20/1.50  sup_num_of_loops:                       242
% 7.20/1.50  sup_fw_superposition:                   589
% 7.20/1.50  sup_bw_superposition:                   3975
% 7.20/1.50  sup_immediate_simplified:               2199
% 7.20/1.50  sup_given_eliminated:                   0
% 7.20/1.50  comparisons_done:                       0
% 7.20/1.50  comparisons_avoided:                    165
% 7.20/1.50  
% 7.20/1.50  ------ Simplifications
% 7.20/1.50  
% 7.20/1.50  
% 7.20/1.50  sim_fw_subset_subsumed:                 1687
% 7.20/1.50  sim_bw_subset_subsumed:                 151
% 7.20/1.50  sim_fw_subsumed:                        314
% 7.20/1.50  sim_bw_subsumed:                        38
% 7.20/1.50  sim_fw_subsumption_res:                 6
% 7.20/1.50  sim_bw_subsumption_res:                 0
% 7.20/1.50  sim_tautology_del:                      35
% 7.20/1.50  sim_eq_tautology_del:                   104
% 7.20/1.50  sim_eq_res_simp:                        34
% 7.20/1.50  sim_fw_demodulated:                     58
% 7.20/1.50  sim_bw_demodulated:                     233
% 7.20/1.50  sim_light_normalised:                   109
% 7.20/1.50  sim_joinable_taut:                      0
% 7.20/1.50  sim_joinable_simp:                      0
% 7.20/1.50  sim_ac_normalised:                      0
% 7.20/1.50  sim_smt_subsumption:                    0
% 7.20/1.50  
%------------------------------------------------------------------------------
