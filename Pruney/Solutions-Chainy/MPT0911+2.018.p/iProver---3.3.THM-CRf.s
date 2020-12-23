%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:04 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 782 expanded)
%              Number of clauses        :   81 ( 230 expanded)
%              Number of leaves         :   17 ( 173 expanded)
%              Depth                    :   25
%              Number of atoms          :  461 (3267 expanded)
%              Number of equality atoms :  329 (2148 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
   => ( k7_mcart_1(sK2,sK3,sK4,sK6) != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK5 = X7
                  | k3_mcart_1(X5,X6,X7) != sK6
                  | ~ m1_subset_1(X7,sK4) )
              | ~ m1_subset_1(X6,sK3) )
          | ~ m1_subset_1(X5,sK2) )
      & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK5 = X7
                | k3_mcart_1(X5,X6,X7) != sK6
                | ~ m1_subset_1(X7,sK4) )
            | ~ m1_subset_1(X6,sK3) )
        | ~ m1_subset_1(X5,sK2) )
    & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f27,f36])).

fof(f60,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f76,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f60,f46])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f34])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f78,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f71])).

fof(f62,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f80,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f73])).

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

fof(f24,plain,(
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

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f53,f46])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X7
      | k3_mcart_1(X5,X6,X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(definition_unfolding,[],[f61,f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_736,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_744,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2345,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_744])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_199,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_zfmisc_1(X2,X3) != X1
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_200,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_735,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_2487,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2345,c_735])).

cnf(c_18,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_738,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_748,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1673,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_748])).

cnf(c_3482,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_2487,c_1673])).

cnf(c_17,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3535,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) != k1_xboole_0
    | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_3482,c_17])).

cnf(c_14,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1214,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14,c_14])).

cnf(c_3619,plain,
    ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(light_normalisation,[status(thm)],[c_3535,c_1214])).

cnf(c_3620,plain,
    ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3619,c_1214])).

cnf(c_3621,plain,
    ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(equality_resolution_simp,[status(thm)],[c_3620])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_33,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_453,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_910,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_911,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_910])).

cnf(c_912,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_913,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_914,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_915,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_741,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3533,plain,
    ( k7_mcart_1(k2_zfmisc_1(sK2,sK3),sK4,X0,X1) = k2_mcart_1(X1)
    | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3482,c_741])).

cnf(c_3646,plain,
    ( k7_mcart_1(k2_zfmisc_1(sK2,sK3),sK4,X0,X1) = k2_mcart_1(X1)
    | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3533,c_1214])).

cnf(c_3544,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_3482,c_17])).

cnf(c_3567,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3544,c_1214])).

cnf(c_3568,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3567])).

cnf(c_12827,plain,
    ( k1_xboole_0 = X0
    | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3646,c_22,c_21,c_20,c_32,c_33,c_911,c_913,c_915,c_3568])).

cnf(c_12828,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_12827])).

cnf(c_13240,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_12828,c_22])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_742,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2486,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2345,c_742])).

cnf(c_2713,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2486,c_735])).

cnf(c_3478,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(superposition,[status(thm)],[c_2713,c_1673])).

cnf(c_23,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ m1_subset_1(X1,sK3)
    | ~ m1_subset_1(X2,sK2)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK6
    | sK5 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_737,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK6
    | sK5 = X2
    | m1_subset_1(X2,sK4) != iProver_top
    | m1_subset_1(X1,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3967,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),X0) != sK6
    | sK5 = X0
    | m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3478,c_737])).

cnf(c_2712,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2486,c_742])).

cnf(c_3479,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2712,c_1673])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_745,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3938,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3479,c_745])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_743,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2711,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2486,c_743])).

cnf(c_3480,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2711,c_1673])).

cnf(c_3953,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3480,c_745])).

cnf(c_4651,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),X0) != sK6
    | sK5 = X0
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3967,c_3938,c_3953])).

cnf(c_13590,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k2_mcart_1(sK6) = sK5
    | m1_subset_1(k2_mcart_1(sK6),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_13240,c_4651])).

cnf(c_3137,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_736,c_741])).

cnf(c_3448,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3137,c_22,c_21,c_20,c_32,c_33,c_911,c_913,c_915])).

cnf(c_19,negated_conjecture,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3451,plain,
    ( k2_mcart_1(sK6) != sK5 ),
    inference(demodulation,[status(thm)],[c_3448,c_19])).

cnf(c_2485,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK4) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2345,c_743])).

cnf(c_3483,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_1673])).

cnf(c_3516,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3483,c_745])).

cnf(c_14173,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13590,c_3451,c_3516])).

cnf(c_14247,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_14173,c_17])).

cnf(c_14255,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14247,c_1214])).

cnf(c_14256,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_14255])).

cnf(c_14510,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3621,c_22,c_21,c_20,c_32,c_33,c_911,c_913,c_915,c_14256])).

cnf(c_14571,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14510,c_20])).

cnf(c_14591,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_14571])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:12:35 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.33  % Running in FOF mode
% 3.57/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/0.99  
% 3.57/0.99  ------  iProver source info
% 3.57/0.99  
% 3.57/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.57/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/0.99  git: non_committed_changes: false
% 3.57/0.99  git: last_make_outside_of_git: false
% 3.57/0.99  
% 3.57/0.99  ------ 
% 3.57/0.99  
% 3.57/0.99  ------ Input Options
% 3.57/0.99  
% 3.57/0.99  --out_options                           all
% 3.57/0.99  --tptp_safe_out                         true
% 3.57/0.99  --problem_path                          ""
% 3.57/0.99  --include_path                          ""
% 3.57/0.99  --clausifier                            res/vclausify_rel
% 3.57/0.99  --clausifier_options                    --mode clausify
% 3.57/0.99  --stdin                                 false
% 3.57/0.99  --stats_out                             all
% 3.57/0.99  
% 3.57/0.99  ------ General Options
% 3.57/0.99  
% 3.57/0.99  --fof                                   false
% 3.57/0.99  --time_out_real                         305.
% 3.57/0.99  --time_out_virtual                      -1.
% 3.57/0.99  --symbol_type_check                     false
% 3.57/0.99  --clausify_out                          false
% 3.57/0.99  --sig_cnt_out                           false
% 3.57/0.99  --trig_cnt_out                          false
% 3.57/0.99  --trig_cnt_out_tolerance                1.
% 3.57/0.99  --trig_cnt_out_sk_spl                   false
% 3.57/0.99  --abstr_cl_out                          false
% 3.57/0.99  
% 3.57/0.99  ------ Global Options
% 3.57/0.99  
% 3.57/0.99  --schedule                              default
% 3.57/0.99  --add_important_lit                     false
% 3.57/0.99  --prop_solver_per_cl                    1000
% 3.57/0.99  --min_unsat_core                        false
% 3.57/0.99  --soft_assumptions                      false
% 3.57/0.99  --soft_lemma_size                       3
% 3.57/0.99  --prop_impl_unit_size                   0
% 3.57/0.99  --prop_impl_unit                        []
% 3.57/0.99  --share_sel_clauses                     true
% 3.57/0.99  --reset_solvers                         false
% 3.57/0.99  --bc_imp_inh                            [conj_cone]
% 3.57/0.99  --conj_cone_tolerance                   3.
% 3.57/0.99  --extra_neg_conj                        none
% 3.57/0.99  --large_theory_mode                     true
% 3.57/0.99  --prolific_symb_bound                   200
% 3.57/0.99  --lt_threshold                          2000
% 3.57/0.99  --clause_weak_htbl                      true
% 3.57/0.99  --gc_record_bc_elim                     false
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing Options
% 3.57/0.99  
% 3.57/0.99  --preprocessing_flag                    true
% 3.57/0.99  --time_out_prep_mult                    0.1
% 3.57/0.99  --splitting_mode                        input
% 3.57/0.99  --splitting_grd                         true
% 3.57/0.99  --splitting_cvd                         false
% 3.57/0.99  --splitting_cvd_svl                     false
% 3.57/0.99  --splitting_nvd                         32
% 3.57/0.99  --sub_typing                            true
% 3.57/0.99  --prep_gs_sim                           true
% 3.57/0.99  --prep_unflatten                        true
% 3.57/0.99  --prep_res_sim                          true
% 3.57/0.99  --prep_upred                            true
% 3.57/0.99  --prep_sem_filter                       exhaustive
% 3.57/0.99  --prep_sem_filter_out                   false
% 3.57/0.99  --pred_elim                             true
% 3.57/0.99  --res_sim_input                         true
% 3.57/0.99  --eq_ax_congr_red                       true
% 3.57/0.99  --pure_diseq_elim                       true
% 3.57/0.99  --brand_transform                       false
% 3.57/0.99  --non_eq_to_eq                          false
% 3.57/0.99  --prep_def_merge                        true
% 3.57/0.99  --prep_def_merge_prop_impl              false
% 3.57/0.99  --prep_def_merge_mbd                    true
% 3.57/0.99  --prep_def_merge_tr_red                 false
% 3.57/0.99  --prep_def_merge_tr_cl                  false
% 3.57/0.99  --smt_preprocessing                     true
% 3.57/0.99  --smt_ac_axioms                         fast
% 3.57/0.99  --preprocessed_out                      false
% 3.57/0.99  --preprocessed_stats                    false
% 3.57/0.99  
% 3.57/0.99  ------ Abstraction refinement Options
% 3.57/0.99  
% 3.57/0.99  --abstr_ref                             []
% 3.57/0.99  --abstr_ref_prep                        false
% 3.57/0.99  --abstr_ref_until_sat                   false
% 3.57/0.99  --abstr_ref_sig_restrict                funpre
% 3.57/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.99  --abstr_ref_under                       []
% 3.57/0.99  
% 3.57/0.99  ------ SAT Options
% 3.57/0.99  
% 3.57/0.99  --sat_mode                              false
% 3.57/0.99  --sat_fm_restart_options                ""
% 3.57/0.99  --sat_gr_def                            false
% 3.57/0.99  --sat_epr_types                         true
% 3.57/0.99  --sat_non_cyclic_types                  false
% 3.57/0.99  --sat_finite_models                     false
% 3.57/0.99  --sat_fm_lemmas                         false
% 3.57/0.99  --sat_fm_prep                           false
% 3.57/0.99  --sat_fm_uc_incr                        true
% 3.57/0.99  --sat_out_model                         small
% 3.57/0.99  --sat_out_clauses                       false
% 3.57/0.99  
% 3.57/0.99  ------ QBF Options
% 3.57/0.99  
% 3.57/0.99  --qbf_mode                              false
% 3.57/0.99  --qbf_elim_univ                         false
% 3.57/0.99  --qbf_dom_inst                          none
% 3.57/0.99  --qbf_dom_pre_inst                      false
% 3.57/0.99  --qbf_sk_in                             false
% 3.57/0.99  --qbf_pred_elim                         true
% 3.57/0.99  --qbf_split                             512
% 3.57/0.99  
% 3.57/0.99  ------ BMC1 Options
% 3.57/0.99  
% 3.57/0.99  --bmc1_incremental                      false
% 3.57/0.99  --bmc1_axioms                           reachable_all
% 3.57/0.99  --bmc1_min_bound                        0
% 3.57/0.99  --bmc1_max_bound                        -1
% 3.57/0.99  --bmc1_max_bound_default                -1
% 3.57/0.99  --bmc1_symbol_reachability              true
% 3.57/0.99  --bmc1_property_lemmas                  false
% 3.57/0.99  --bmc1_k_induction                      false
% 3.57/0.99  --bmc1_non_equiv_states                 false
% 3.57/0.99  --bmc1_deadlock                         false
% 3.57/0.99  --bmc1_ucm                              false
% 3.57/0.99  --bmc1_add_unsat_core                   none
% 3.57/0.99  --bmc1_unsat_core_children              false
% 3.57/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.99  --bmc1_out_stat                         full
% 3.57/0.99  --bmc1_ground_init                      false
% 3.57/0.99  --bmc1_pre_inst_next_state              false
% 3.57/0.99  --bmc1_pre_inst_state                   false
% 3.57/0.99  --bmc1_pre_inst_reach_state             false
% 3.57/0.99  --bmc1_out_unsat_core                   false
% 3.57/0.99  --bmc1_aig_witness_out                  false
% 3.57/0.99  --bmc1_verbose                          false
% 3.57/0.99  --bmc1_dump_clauses_tptp                false
% 3.57/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.99  --bmc1_dump_file                        -
% 3.57/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.99  --bmc1_ucm_extend_mode                  1
% 3.57/0.99  --bmc1_ucm_init_mode                    2
% 3.57/0.99  --bmc1_ucm_cone_mode                    none
% 3.57/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.99  --bmc1_ucm_relax_model                  4
% 3.57/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.99  --bmc1_ucm_layered_model                none
% 3.57/0.99  --bmc1_ucm_max_lemma_size               10
% 3.57/0.99  
% 3.57/0.99  ------ AIG Options
% 3.57/0.99  
% 3.57/0.99  --aig_mode                              false
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation Options
% 3.57/0.99  
% 3.57/0.99  --instantiation_flag                    true
% 3.57/0.99  --inst_sos_flag                         false
% 3.57/0.99  --inst_sos_phase                        true
% 3.57/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel_side                     num_symb
% 3.57/0.99  --inst_solver_per_active                1400
% 3.57/0.99  --inst_solver_calls_frac                1.
% 3.57/0.99  --inst_passive_queue_type               priority_queues
% 3.57/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.99  --inst_passive_queues_freq              [25;2]
% 3.57/0.99  --inst_dismatching                      true
% 3.57/0.99  --inst_eager_unprocessed_to_passive     true
% 3.57/0.99  --inst_prop_sim_given                   true
% 3.57/0.99  --inst_prop_sim_new                     false
% 3.57/0.99  --inst_subs_new                         false
% 3.57/0.99  --inst_eq_res_simp                      false
% 3.57/0.99  --inst_subs_given                       false
% 3.57/0.99  --inst_orphan_elimination               true
% 3.57/0.99  --inst_learning_loop_flag               true
% 3.57/0.99  --inst_learning_start                   3000
% 3.57/0.99  --inst_learning_factor                  2
% 3.57/0.99  --inst_start_prop_sim_after_learn       3
% 3.57/0.99  --inst_sel_renew                        solver
% 3.57/0.99  --inst_lit_activity_flag                true
% 3.57/0.99  --inst_restr_to_given                   false
% 3.57/0.99  --inst_activity_threshold               500
% 3.57/0.99  --inst_out_proof                        true
% 3.57/0.99  
% 3.57/0.99  ------ Resolution Options
% 3.57/0.99  
% 3.57/0.99  --resolution_flag                       true
% 3.57/0.99  --res_lit_sel                           adaptive
% 3.57/0.99  --res_lit_sel_side                      none
% 3.57/0.99  --res_ordering                          kbo
% 3.57/0.99  --res_to_prop_solver                    active
% 3.57/0.99  --res_prop_simpl_new                    false
% 3.57/0.99  --res_prop_simpl_given                  true
% 3.57/0.99  --res_passive_queue_type                priority_queues
% 3.57/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.99  --res_passive_queues_freq               [15;5]
% 3.57/0.99  --res_forward_subs                      full
% 3.57/0.99  --res_backward_subs                     full
% 3.57/0.99  --res_forward_subs_resolution           true
% 3.57/0.99  --res_backward_subs_resolution          true
% 3.57/0.99  --res_orphan_elimination                true
% 3.57/0.99  --res_time_limit                        2.
% 3.57/0.99  --res_out_proof                         true
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Options
% 3.57/0.99  
% 3.57/0.99  --superposition_flag                    true
% 3.57/0.99  --sup_passive_queue_type                priority_queues
% 3.57/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.99  --demod_completeness_check              fast
% 3.57/0.99  --demod_use_ground                      true
% 3.57/0.99  --sup_to_prop_solver                    passive
% 3.57/0.99  --sup_prop_simpl_new                    true
% 3.57/0.99  --sup_prop_simpl_given                  true
% 3.57/0.99  --sup_fun_splitting                     false
% 3.57/0.99  --sup_smt_interval                      50000
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Simplification Setup
% 3.57/0.99  
% 3.57/0.99  --sup_indices_passive                   []
% 3.57/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_full_bw                           [BwDemod]
% 3.57/0.99  --sup_immed_triv                        [TrivRules]
% 3.57/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_immed_bw_main                     []
% 3.57/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.99  
% 3.57/0.99  ------ Combination Options
% 3.57/0.99  
% 3.57/0.99  --comb_res_mult                         3
% 3.57/0.99  --comb_sup_mult                         2
% 3.57/0.99  --comb_inst_mult                        10
% 3.57/0.99  
% 3.57/0.99  ------ Debug Options
% 3.57/0.99  
% 3.57/0.99  --dbg_backtrace                         false
% 3.57/0.99  --dbg_dump_prop_clauses                 false
% 3.57/0.99  --dbg_dump_prop_clauses_file            -
% 3.57/0.99  --dbg_out_stat                          false
% 3.57/0.99  ------ Parsing...
% 3.57/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/0.99  ------ Proving...
% 3.57/0.99  ------ Problem Properties 
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  clauses                                 24
% 3.57/0.99  conjectures                             6
% 3.57/0.99  EPR                                     7
% 3.57/0.99  Horn                                    17
% 3.57/0.99  unary                                   11
% 3.57/0.99  binary                                  7
% 3.57/0.99  lits                                    53
% 3.57/0.99  lits eq                                 29
% 3.57/0.99  fd_pure                                 0
% 3.57/0.99  fd_pseudo                               0
% 3.57/0.99  fd_cond                                 6
% 3.57/0.99  fd_pseudo_cond                          0
% 3.57/0.99  AC symbols                              0
% 3.57/0.99  
% 3.57/0.99  ------ Schedule dynamic 5 is on 
% 3.57/0.99  
% 3.57/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  ------ 
% 3.57/0.99  Current options:
% 3.57/0.99  ------ 
% 3.57/0.99  
% 3.57/0.99  ------ Input Options
% 3.57/0.99  
% 3.57/0.99  --out_options                           all
% 3.57/0.99  --tptp_safe_out                         true
% 3.57/0.99  --problem_path                          ""
% 3.57/0.99  --include_path                          ""
% 3.57/0.99  --clausifier                            res/vclausify_rel
% 3.57/0.99  --clausifier_options                    --mode clausify
% 3.57/0.99  --stdin                                 false
% 3.57/0.99  --stats_out                             all
% 3.57/0.99  
% 3.57/0.99  ------ General Options
% 3.57/0.99  
% 3.57/0.99  --fof                                   false
% 3.57/0.99  --time_out_real                         305.
% 3.57/0.99  --time_out_virtual                      -1.
% 3.57/0.99  --symbol_type_check                     false
% 3.57/0.99  --clausify_out                          false
% 3.57/0.99  --sig_cnt_out                           false
% 3.57/0.99  --trig_cnt_out                          false
% 3.57/0.99  --trig_cnt_out_tolerance                1.
% 3.57/0.99  --trig_cnt_out_sk_spl                   false
% 3.57/0.99  --abstr_cl_out                          false
% 3.57/0.99  
% 3.57/0.99  ------ Global Options
% 3.57/0.99  
% 3.57/0.99  --schedule                              default
% 3.57/0.99  --add_important_lit                     false
% 3.57/0.99  --prop_solver_per_cl                    1000
% 3.57/0.99  --min_unsat_core                        false
% 3.57/0.99  --soft_assumptions                      false
% 3.57/0.99  --soft_lemma_size                       3
% 3.57/0.99  --prop_impl_unit_size                   0
% 3.57/0.99  --prop_impl_unit                        []
% 3.57/0.99  --share_sel_clauses                     true
% 3.57/0.99  --reset_solvers                         false
% 3.57/0.99  --bc_imp_inh                            [conj_cone]
% 3.57/0.99  --conj_cone_tolerance                   3.
% 3.57/0.99  --extra_neg_conj                        none
% 3.57/0.99  --large_theory_mode                     true
% 3.57/0.99  --prolific_symb_bound                   200
% 3.57/0.99  --lt_threshold                          2000
% 3.57/0.99  --clause_weak_htbl                      true
% 3.57/0.99  --gc_record_bc_elim                     false
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing Options
% 3.57/0.99  
% 3.57/0.99  --preprocessing_flag                    true
% 3.57/0.99  --time_out_prep_mult                    0.1
% 3.57/0.99  --splitting_mode                        input
% 3.57/0.99  --splitting_grd                         true
% 3.57/0.99  --splitting_cvd                         false
% 3.57/0.99  --splitting_cvd_svl                     false
% 3.57/0.99  --splitting_nvd                         32
% 3.57/0.99  --sub_typing                            true
% 3.57/0.99  --prep_gs_sim                           true
% 3.57/0.99  --prep_unflatten                        true
% 3.57/0.99  --prep_res_sim                          true
% 3.57/0.99  --prep_upred                            true
% 3.57/0.99  --prep_sem_filter                       exhaustive
% 3.57/0.99  --prep_sem_filter_out                   false
% 3.57/0.99  --pred_elim                             true
% 3.57/0.99  --res_sim_input                         true
% 3.57/0.99  --eq_ax_congr_red                       true
% 3.57/0.99  --pure_diseq_elim                       true
% 3.57/0.99  --brand_transform                       false
% 3.57/0.99  --non_eq_to_eq                          false
% 3.57/0.99  --prep_def_merge                        true
% 3.57/0.99  --prep_def_merge_prop_impl              false
% 3.57/0.99  --prep_def_merge_mbd                    true
% 3.57/0.99  --prep_def_merge_tr_red                 false
% 3.57/0.99  --prep_def_merge_tr_cl                  false
% 3.57/0.99  --smt_preprocessing                     true
% 3.57/0.99  --smt_ac_axioms                         fast
% 3.57/0.99  --preprocessed_out                      false
% 3.57/0.99  --preprocessed_stats                    false
% 3.57/0.99  
% 3.57/0.99  ------ Abstraction refinement Options
% 3.57/0.99  
% 3.57/0.99  --abstr_ref                             []
% 3.57/0.99  --abstr_ref_prep                        false
% 3.57/0.99  --abstr_ref_until_sat                   false
% 3.57/0.99  --abstr_ref_sig_restrict                funpre
% 3.57/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.99  --abstr_ref_under                       []
% 3.57/0.99  
% 3.57/0.99  ------ SAT Options
% 3.57/0.99  
% 3.57/0.99  --sat_mode                              false
% 3.57/0.99  --sat_fm_restart_options                ""
% 3.57/0.99  --sat_gr_def                            false
% 3.57/0.99  --sat_epr_types                         true
% 3.57/0.99  --sat_non_cyclic_types                  false
% 3.57/0.99  --sat_finite_models                     false
% 3.57/0.99  --sat_fm_lemmas                         false
% 3.57/0.99  --sat_fm_prep                           false
% 3.57/0.99  --sat_fm_uc_incr                        true
% 3.57/0.99  --sat_out_model                         small
% 3.57/0.99  --sat_out_clauses                       false
% 3.57/0.99  
% 3.57/0.99  ------ QBF Options
% 3.57/0.99  
% 3.57/0.99  --qbf_mode                              false
% 3.57/0.99  --qbf_elim_univ                         false
% 3.57/0.99  --qbf_dom_inst                          none
% 3.57/0.99  --qbf_dom_pre_inst                      false
% 3.57/0.99  --qbf_sk_in                             false
% 3.57/0.99  --qbf_pred_elim                         true
% 3.57/0.99  --qbf_split                             512
% 3.57/0.99  
% 3.57/0.99  ------ BMC1 Options
% 3.57/0.99  
% 3.57/0.99  --bmc1_incremental                      false
% 3.57/0.99  --bmc1_axioms                           reachable_all
% 3.57/0.99  --bmc1_min_bound                        0
% 3.57/0.99  --bmc1_max_bound                        -1
% 3.57/0.99  --bmc1_max_bound_default                -1
% 3.57/0.99  --bmc1_symbol_reachability              true
% 3.57/0.99  --bmc1_property_lemmas                  false
% 3.57/0.99  --bmc1_k_induction                      false
% 3.57/0.99  --bmc1_non_equiv_states                 false
% 3.57/0.99  --bmc1_deadlock                         false
% 3.57/0.99  --bmc1_ucm                              false
% 3.57/0.99  --bmc1_add_unsat_core                   none
% 3.57/0.99  --bmc1_unsat_core_children              false
% 3.57/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.99  --bmc1_out_stat                         full
% 3.57/0.99  --bmc1_ground_init                      false
% 3.57/0.99  --bmc1_pre_inst_next_state              false
% 3.57/0.99  --bmc1_pre_inst_state                   false
% 3.57/0.99  --bmc1_pre_inst_reach_state             false
% 3.57/0.99  --bmc1_out_unsat_core                   false
% 3.57/0.99  --bmc1_aig_witness_out                  false
% 3.57/0.99  --bmc1_verbose                          false
% 3.57/0.99  --bmc1_dump_clauses_tptp                false
% 3.57/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.99  --bmc1_dump_file                        -
% 3.57/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.99  --bmc1_ucm_extend_mode                  1
% 3.57/0.99  --bmc1_ucm_init_mode                    2
% 3.57/0.99  --bmc1_ucm_cone_mode                    none
% 3.57/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.99  --bmc1_ucm_relax_model                  4
% 3.57/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.99  --bmc1_ucm_layered_model                none
% 3.57/0.99  --bmc1_ucm_max_lemma_size               10
% 3.57/0.99  
% 3.57/0.99  ------ AIG Options
% 3.57/0.99  
% 3.57/0.99  --aig_mode                              false
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation Options
% 3.57/0.99  
% 3.57/0.99  --instantiation_flag                    true
% 3.57/0.99  --inst_sos_flag                         false
% 3.57/0.99  --inst_sos_phase                        true
% 3.57/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.99  --inst_lit_sel_side                     none
% 3.57/0.99  --inst_solver_per_active                1400
% 3.57/0.99  --inst_solver_calls_frac                1.
% 3.57/0.99  --inst_passive_queue_type               priority_queues
% 3.57/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.99  --inst_passive_queues_freq              [25;2]
% 3.57/0.99  --inst_dismatching                      true
% 3.57/0.99  --inst_eager_unprocessed_to_passive     true
% 3.57/0.99  --inst_prop_sim_given                   true
% 3.57/0.99  --inst_prop_sim_new                     false
% 3.57/0.99  --inst_subs_new                         false
% 3.57/0.99  --inst_eq_res_simp                      false
% 3.57/0.99  --inst_subs_given                       false
% 3.57/0.99  --inst_orphan_elimination               true
% 3.57/0.99  --inst_learning_loop_flag               true
% 3.57/0.99  --inst_learning_start                   3000
% 3.57/0.99  --inst_learning_factor                  2
% 3.57/0.99  --inst_start_prop_sim_after_learn       3
% 3.57/0.99  --inst_sel_renew                        solver
% 3.57/0.99  --inst_lit_activity_flag                true
% 3.57/0.99  --inst_restr_to_given                   false
% 3.57/0.99  --inst_activity_threshold               500
% 3.57/0.99  --inst_out_proof                        true
% 3.57/0.99  
% 3.57/0.99  ------ Resolution Options
% 3.57/0.99  
% 3.57/0.99  --resolution_flag                       false
% 3.57/0.99  --res_lit_sel                           adaptive
% 3.57/0.99  --res_lit_sel_side                      none
% 3.57/0.99  --res_ordering                          kbo
% 3.57/0.99  --res_to_prop_solver                    active
% 3.57/0.99  --res_prop_simpl_new                    false
% 3.57/0.99  --res_prop_simpl_given                  true
% 3.57/0.99  --res_passive_queue_type                priority_queues
% 3.57/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.99  --res_passive_queues_freq               [15;5]
% 3.57/0.99  --res_forward_subs                      full
% 3.57/0.99  --res_backward_subs                     full
% 3.57/0.99  --res_forward_subs_resolution           true
% 3.57/0.99  --res_backward_subs_resolution          true
% 3.57/0.99  --res_orphan_elimination                true
% 3.57/0.99  --res_time_limit                        2.
% 3.57/0.99  --res_out_proof                         true
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Options
% 3.57/0.99  
% 3.57/0.99  --superposition_flag                    true
% 3.57/0.99  --sup_passive_queue_type                priority_queues
% 3.57/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.99  --demod_completeness_check              fast
% 3.57/0.99  --demod_use_ground                      true
% 3.57/0.99  --sup_to_prop_solver                    passive
% 3.57/0.99  --sup_prop_simpl_new                    true
% 3.57/0.99  --sup_prop_simpl_given                  true
% 3.57/0.99  --sup_fun_splitting                     false
% 3.57/0.99  --sup_smt_interval                      50000
% 3.57/0.99  
% 3.57/0.99  ------ Superposition Simplification Setup
% 3.57/0.99  
% 3.57/0.99  --sup_indices_passive                   []
% 3.57/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_full_bw                           [BwDemod]
% 3.57/0.99  --sup_immed_triv                        [TrivRules]
% 3.57/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_immed_bw_main                     []
% 3.57/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.99  
% 3.57/0.99  ------ Combination Options
% 3.57/0.99  
% 3.57/0.99  --comb_res_mult                         3
% 3.57/0.99  --comb_sup_mult                         2
% 3.57/0.99  --comb_inst_mult                        10
% 3.57/0.99  
% 3.57/0.99  ------ Debug Options
% 3.57/0.99  
% 3.57/0.99  --dbg_backtrace                         false
% 3.57/0.99  --dbg_dump_prop_clauses                 false
% 3.57/0.99  --dbg_dump_prop_clauses_file            -
% 3.57/0.99  --dbg_out_stat                          false
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  ------ Proving...
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  % SZS status Theorem for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99   Resolution empty clause
% 3.57/0.99  
% 3.57/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  fof(f15,conjecture,(
% 3.57/0.99    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f16,negated_conjecture,(
% 3.57/0.99    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.57/0.99    inference(negated_conjecture,[],[f15])).
% 3.57/0.99  
% 3.57/0.99  fof(f26,plain,(
% 3.57/0.99    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.57/0.99    inference(ennf_transformation,[],[f16])).
% 3.57/0.99  
% 3.57/0.99  fof(f27,plain,(
% 3.57/0.99    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.57/0.99    inference(flattening,[],[f26])).
% 3.57/0.99  
% 3.57/0.99  fof(f36,plain,(
% 3.57/0.99    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)))),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f37,plain,(
% 3.57/0.99    k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 3.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f27,f36])).
% 3.57/0.99  
% 3.57/0.99  fof(f60,plain,(
% 3.57/0.99    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 3.57/0.99    inference(cnf_transformation,[],[f37])).
% 3.57/0.99  
% 3.57/0.99  fof(f8,axiom,(
% 3.57/0.99    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f46,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f8])).
% 3.57/0.99  
% 3.57/0.99  fof(f76,plain,(
% 3.57/0.99    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 3.57/0.99    inference(definition_unfolding,[],[f60,f46])).
% 3.57/0.99  
% 3.57/0.99  fof(f5,axiom,(
% 3.57/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f19,plain,(
% 3.57/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.57/0.99    inference(ennf_transformation,[],[f5])).
% 3.57/0.99  
% 3.57/0.99  fof(f20,plain,(
% 3.57/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.57/0.99    inference(flattening,[],[f19])).
% 3.57/0.99  
% 3.57/0.99  fof(f43,plain,(
% 3.57/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f20])).
% 3.57/0.99  
% 3.57/0.99  fof(f6,axiom,(
% 3.57/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f44,plain,(
% 3.57/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f6])).
% 3.57/0.99  
% 3.57/0.99  fof(f11,axiom,(
% 3.57/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f22,plain,(
% 3.57/0.99    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 3.57/0.99    inference(ennf_transformation,[],[f11])).
% 3.57/0.99  
% 3.57/0.99  fof(f23,plain,(
% 3.57/0.99    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 3.57/0.99    inference(flattening,[],[f22])).
% 3.57/0.99  
% 3.57/0.99  fof(f50,plain,(
% 3.57/0.99    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f23])).
% 3.57/0.99  
% 3.57/0.99  fof(f14,axiom,(
% 3.57/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f17,plain,(
% 3.57/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.57/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.57/0.99  
% 3.57/0.99  fof(f25,plain,(
% 3.57/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.57/0.99    inference(ennf_transformation,[],[f17])).
% 3.57/0.99  
% 3.57/0.99  fof(f34,plain,(
% 3.57/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f35,plain,(
% 3.57/0.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f34])).
% 3.57/0.99  
% 3.57/0.99  fof(f59,plain,(
% 3.57/0.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.57/0.99    inference(cnf_transformation,[],[f35])).
% 3.57/0.99  
% 3.57/0.99  fof(f1,axiom,(
% 3.57/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f28,plain,(
% 3.57/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.57/0.99    inference(nnf_transformation,[],[f1])).
% 3.57/0.99  
% 3.57/0.99  fof(f29,plain,(
% 3.57/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.57/0.99    inference(rectify,[],[f28])).
% 3.57/0.99  
% 3.57/0.99  fof(f30,plain,(
% 3.57/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f31,plain,(
% 3.57/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.57/0.99  
% 3.57/0.99  fof(f38,plain,(
% 3.57/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f31])).
% 3.57/0.99  
% 3.57/0.99  fof(f13,axiom,(
% 3.57/0.99    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f32,plain,(
% 3.57/0.99    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.57/0.99    inference(nnf_transformation,[],[f13])).
% 3.57/0.99  
% 3.57/0.99  fof(f33,plain,(
% 3.57/0.99    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.57/0.99    inference(flattening,[],[f32])).
% 3.57/0.99  
% 3.57/0.99  fof(f54,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.57/0.99    inference(cnf_transformation,[],[f33])).
% 3.57/0.99  
% 3.57/0.99  fof(f9,axiom,(
% 3.57/0.99    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f47,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f9])).
% 3.57/0.99  
% 3.57/0.99  fof(f66,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f47,f46])).
% 3.57/0.99  
% 3.57/0.99  fof(f74,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.57/0.99    inference(definition_unfolding,[],[f54,f66])).
% 3.57/0.99  
% 3.57/0.99  fof(f57,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f33])).
% 3.57/0.99  
% 3.57/0.99  fof(f71,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f57,f66])).
% 3.57/0.99  
% 3.57/0.99  fof(f78,plain,(
% 3.57/0.99    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 3.57/0.99    inference(equality_resolution,[],[f71])).
% 3.57/0.99  
% 3.57/0.99  fof(f62,plain,(
% 3.57/0.99    k1_xboole_0 != sK2),
% 3.57/0.99    inference(cnf_transformation,[],[f37])).
% 3.57/0.99  
% 3.57/0.99  fof(f63,plain,(
% 3.57/0.99    k1_xboole_0 != sK3),
% 3.57/0.99    inference(cnf_transformation,[],[f37])).
% 3.57/0.99  
% 3.57/0.99  fof(f64,plain,(
% 3.57/0.99    k1_xboole_0 != sK4),
% 3.57/0.99    inference(cnf_transformation,[],[f37])).
% 3.57/0.99  
% 3.57/0.99  fof(f55,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f33])).
% 3.57/0.99  
% 3.57/0.99  fof(f73,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f55,f66])).
% 3.57/0.99  
% 3.57/0.99  fof(f80,plain,(
% 3.57/0.99    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 3.57/0.99    inference(equality_resolution,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f12,axiom,(
% 3.57/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f24,plain,(
% 3.57/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.57/0.99    inference(ennf_transformation,[],[f12])).
% 3.57/0.99  
% 3.57/0.99  fof(f53,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.57/0.99    inference(cnf_transformation,[],[f24])).
% 3.57/0.99  
% 3.57/0.99  fof(f67,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.57/0.99    inference(definition_unfolding,[],[f53,f46])).
% 3.57/0.99  
% 3.57/0.99  fof(f10,axiom,(
% 3.57/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f21,plain,(
% 3.57/0.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.57/0.99    inference(ennf_transformation,[],[f10])).
% 3.57/0.99  
% 3.57/0.99  fof(f48,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f21])).
% 3.57/0.99  
% 3.57/0.99  fof(f61,plain,(
% 3.57/0.99    ( ! [X6,X7,X5] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f37])).
% 3.57/0.99  
% 3.57/0.99  fof(f7,axiom,(
% 3.57/0.99    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f45,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f7])).
% 3.57/0.99  
% 3.57/0.99  fof(f75,plain,(
% 3.57/0.99    ( ! [X6,X7,X5] : (sK5 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 3.57/0.99    inference(definition_unfolding,[],[f61,f45])).
% 3.57/0.99  
% 3.57/0.99  fof(f4,axiom,(
% 3.57/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f18,plain,(
% 3.57/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.57/0.99    inference(ennf_transformation,[],[f4])).
% 3.57/0.99  
% 3.57/0.99  fof(f42,plain,(
% 3.57/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f18])).
% 3.57/0.99  
% 3.57/0.99  fof(f49,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.57/0.99    inference(cnf_transformation,[],[f21])).
% 3.57/0.99  
% 3.57/0.99  fof(f65,plain,(
% 3.57/0.99    k7_mcart_1(sK2,sK3,sK4,sK6) != sK5),
% 3.57/0.99    inference(cnf_transformation,[],[f37])).
% 3.57/0.99  
% 3.57/0.99  cnf(c_24,negated_conjecture,
% 3.57/0.99      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 3.57/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_736,plain,
% 3.57/0.99      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_744,plain,
% 3.57/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.57/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.57/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2345,plain,
% 3.57/0.99      ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top
% 3.57/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_736,c_744]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6,plain,
% 3.57/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.57/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_9,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,X1)
% 3.57/0.99      | ~ v1_relat_1(X1)
% 3.57/0.99      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_199,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,X1)
% 3.57/0.99      | k2_zfmisc_1(X2,X3) != X1
% 3.57/0.99      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_9]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_200,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.57/0.99      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_199]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_735,plain,
% 3.57/0.99      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.57/0.99      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_200]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2487,plain,
% 3.57/0.99      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.57/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2345,c_735]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_18,plain,
% 3.57/0.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_738,plain,
% 3.57/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_748,plain,
% 3.57/0.99      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1673,plain,
% 3.57/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_738,c_748]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3482,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.57/0.99      | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2487,c_1673]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_17,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X2
% 3.57/0.99      | k1_xboole_0 = X1
% 3.57/0.99      | k1_xboole_0 = X0
% 3.57/0.99      | k1_xboole_0 = X3 ),
% 3.57/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3535,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) != k1_xboole_0
% 3.57/0.99      | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 3.57/0.99      | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.57/0.99      | sK4 = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X1
% 3.57/0.99      | k1_xboole_0 = X0 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3482,c_17]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_14,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_1214,plain,
% 3.57/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_14,c_14]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3619,plain,
% 3.57/0.99      ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 3.57/0.99      | k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 3.57/0.99      | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.57/0.99      | sK4 = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X0
% 3.57/0.99      | k1_xboole_0 = X1 ),
% 3.57/0.99      inference(light_normalisation,[status(thm)],[c_3535,c_1214]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3620,plain,
% 3.57/0.99      ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 3.57/0.99      | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.57/0.99      | sK4 = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X0
% 3.57/0.99      | k1_xboole_0 = X1
% 3.57/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_3619,c_1214]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3621,plain,
% 3.57/0.99      ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 3.57/0.99      | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.57/0.99      | sK4 = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X0
% 3.57/0.99      | k1_xboole_0 = X1 ),
% 3.57/0.99      inference(equality_resolution_simp,[status(thm)],[c_3620]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_22,negated_conjecture,
% 3.57/0.99      ( k1_xboole_0 != sK2 ),
% 3.57/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_21,negated_conjecture,
% 3.57/0.99      ( k1_xboole_0 != sK3 ),
% 3.57/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_20,negated_conjecture,
% 3.57/0.99      ( k1_xboole_0 != sK4 ),
% 3.57/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_32,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_16,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_33,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_453,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_910,plain,
% 3.57/0.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_453]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_911,plain,
% 3.57/0.99      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_910]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_912,plain,
% 3.57/0.99      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_453]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_913,plain,
% 3.57/0.99      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_912]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_914,plain,
% 3.57/0.99      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_453]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_915,plain,
% 3.57/0.99      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_914]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10,plain,
% 3.57/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.57/0.99      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.57/0.99      | k1_xboole_0 = X3
% 3.57/0.99      | k1_xboole_0 = X2
% 3.57/0.99      | k1_xboole_0 = X1 ),
% 3.57/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_741,plain,
% 3.57/0.99      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.57/0.99      | k1_xboole_0 = X0
% 3.57/0.99      | k1_xboole_0 = X1
% 3.57/0.99      | k1_xboole_0 = X2
% 3.57/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3533,plain,
% 3.57/0.99      ( k7_mcart_1(k2_zfmisc_1(sK2,sK3),sK4,X0,X1) = k2_mcart_1(X1)
% 3.57/0.99      | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 3.57/0.99      | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.57/0.99      | sK4 = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X0
% 3.57/0.99      | m1_subset_1(X1,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3482,c_741]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3646,plain,
% 3.57/0.99      ( k7_mcart_1(k2_zfmisc_1(sK2,sK3),sK4,X0,X1) = k2_mcart_1(X1)
% 3.57/0.99      | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 3.57/0.99      | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.57/0.99      | sK4 = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X0
% 3.57/0.99      | m1_subset_1(X1,k1_xboole_0) != iProver_top ),
% 3.57/0.99      inference(light_normalisation,[status(thm)],[c_3533,c_1214]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3544,plain,
% 3.57/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 3.57/0.99      | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.57/0.99      | sK4 = k1_xboole_0
% 3.57/0.99      | sK3 = k1_xboole_0
% 3.57/0.99      | sK2 = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X0 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3482,c_17]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3567,plain,
% 3.57/0.99      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.57/0.99      | sK4 = k1_xboole_0
% 3.57/0.99      | sK3 = k1_xboole_0
% 3.57/0.99      | sK2 = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X0
% 3.57/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.57/0.99      inference(light_normalisation,[status(thm)],[c_3544,c_1214]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3568,plain,
% 3.57/0.99      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.57/0.99      | sK4 = k1_xboole_0
% 3.57/0.99      | sK3 = k1_xboole_0
% 3.57/0.99      | sK2 = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X0 ),
% 3.57/0.99      inference(equality_resolution_simp,[status(thm)],[c_3567]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_12827,plain,
% 3.57/0.99      ( k1_xboole_0 = X0 | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_3646,c_22,c_21,c_20,c_32,c_33,c_911,c_913,c_915,c_3568]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_12828,plain,
% 3.57/0.99      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 | k1_xboole_0 = X0 ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_12827]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_13240,plain,
% 3.57/0.99      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_12828,c_22]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_8,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_742,plain,
% 3.57/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.57/0.99      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2486,plain,
% 3.57/0.99      ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top
% 3.57/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2345,c_742]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2713,plain,
% 3.57/0.99      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 3.57/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2486,c_735]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3478,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.57/0.99      | k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2713,c_1673]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_23,negated_conjecture,
% 3.57/0.99      ( ~ m1_subset_1(X0,sK4)
% 3.57/0.99      | ~ m1_subset_1(X1,sK3)
% 3.57/0.99      | ~ m1_subset_1(X2,sK2)
% 3.57/0.99      | k4_tarski(k4_tarski(X2,X1),X0) != sK6
% 3.57/0.99      | sK5 = X0 ),
% 3.57/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_737,plain,
% 3.57/0.99      ( k4_tarski(k4_tarski(X0,X1),X2) != sK6
% 3.57/0.99      | sK5 = X2
% 3.57/0.99      | m1_subset_1(X2,sK4) != iProver_top
% 3.57/0.99      | m1_subset_1(X1,sK3) != iProver_top
% 3.57/0.99      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3967,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.57/0.99      | k4_tarski(k1_mcart_1(sK6),X0) != sK6
% 3.57/0.99      | sK5 = X0
% 3.57/0.99      | m1_subset_1(X0,sK4) != iProver_top
% 3.57/0.99      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) != iProver_top
% 3.57/0.99      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3478,c_737]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2712,plain,
% 3.57/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top
% 3.57/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2486,c_742]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3479,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.57/0.99      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2712,c_1673]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4,plain,
% 3.57/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_745,plain,
% 3.57/0.99      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3938,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.57/0.99      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3479,c_745]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7,plain,
% 3.57/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.57/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_743,plain,
% 3.57/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.57/0.99      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2711,plain,
% 3.57/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top
% 3.57/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2486,c_743]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3480,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.57/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2711,c_1673]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3953,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.57/0.99      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3480,c_745]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4651,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.57/0.99      | k4_tarski(k1_mcart_1(sK6),X0) != sK6
% 3.57/0.99      | sK5 = X0
% 3.57/0.99      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_3967,c_3938,c_3953]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_13590,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.57/0.99      | k2_mcart_1(sK6) = sK5
% 3.57/0.99      | m1_subset_1(k2_mcart_1(sK6),sK4) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_13240,c_4651]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3137,plain,
% 3.57/0.99      ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
% 3.57/0.99      | sK4 = k1_xboole_0
% 3.57/0.99      | sK3 = k1_xboole_0
% 3.57/0.99      | sK2 = k1_xboole_0 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_736,c_741]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3448,plain,
% 3.57/0.99      ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_3137,c_22,c_21,c_20,c_32,c_33,c_911,c_913,c_915]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_19,negated_conjecture,
% 3.57/0.99      ( k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
% 3.57/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3451,plain,
% 3.57/0.99      ( k2_mcart_1(sK6) != sK5 ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_3448,c_19]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2485,plain,
% 3.57/0.99      ( r2_hidden(k2_mcart_1(sK6),sK4) = iProver_top
% 3.57/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2345,c_743]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3483,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.57/0.99      | r2_hidden(k2_mcart_1(sK6),sK4) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_2485,c_1673]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3516,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.57/0.99      | m1_subset_1(k2_mcart_1(sK6),sK4) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3483,c_745]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_14173,plain,
% 3.57/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_13590,c_3451,c_3516]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_14247,plain,
% 3.57/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 3.57/0.99      | sK4 = k1_xboole_0
% 3.57/0.99      | sK3 = k1_xboole_0
% 3.57/0.99      | sK2 = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X0 ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_14173,c_17]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_14255,plain,
% 3.57/0.99      ( sK4 = k1_xboole_0
% 3.57/0.99      | sK3 = k1_xboole_0
% 3.57/0.99      | sK2 = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X0
% 3.57/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.57/0.99      inference(light_normalisation,[status(thm)],[c_14247,c_1214]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_14256,plain,
% 3.57/0.99      ( sK4 = k1_xboole_0
% 3.57/0.99      | sK3 = k1_xboole_0
% 3.57/0.99      | sK2 = k1_xboole_0
% 3.57/0.99      | k1_xboole_0 = X0 ),
% 3.57/0.99      inference(equality_resolution_simp,[status(thm)],[c_14255]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_14510,plain,
% 3.57/0.99      ( k1_xboole_0 = X0 ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_3621,c_22,c_21,c_20,c_32,c_33,c_911,c_913,c_915,c_14256]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_14571,plain,
% 3.57/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_14510,c_20]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_14591,plain,
% 3.57/0.99      ( $false ),
% 3.57/0.99      inference(equality_resolution_simp,[status(thm)],[c_14571]) ).
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  ------                               Statistics
% 3.57/0.99  
% 3.57/0.99  ------ General
% 3.57/0.99  
% 3.57/0.99  abstr_ref_over_cycles:                  0
% 3.57/0.99  abstr_ref_under_cycles:                 0
% 3.57/0.99  gc_basic_clause_elim:                   0
% 3.57/0.99  forced_gc_time:                         0
% 3.57/0.99  parsing_time:                           0.013
% 3.57/0.99  unif_index_cands_time:                  0.
% 3.57/0.99  unif_index_add_time:                    0.
% 3.57/0.99  orderings_time:                         0.
% 3.57/0.99  out_proof_time:                         0.011
% 3.57/0.99  total_time:                             0.387
% 3.57/0.99  num_of_symbols:                         50
% 3.57/0.99  num_of_terms:                           12076
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing
% 3.57/0.99  
% 3.57/0.99  num_of_splits:                          0
% 3.57/0.99  num_of_split_atoms:                     0
% 3.57/0.99  num_of_reused_defs:                     0
% 3.57/0.99  num_eq_ax_congr_red:                    30
% 3.57/0.99  num_of_sem_filtered_clauses:            1
% 3.57/0.99  num_of_subtypes:                        0
% 3.57/0.99  monotx_restored_types:                  0
% 3.57/0.99  sat_num_of_epr_types:                   0
% 3.57/0.99  sat_num_of_non_cyclic_types:            0
% 3.57/0.99  sat_guarded_non_collapsed_types:        0
% 3.57/0.99  num_pure_diseq_elim:                    0
% 3.57/0.99  simp_replaced_by:                       0
% 3.57/0.99  res_preprocessed:                       118
% 3.57/0.99  prep_upred:                             0
% 3.57/0.99  prep_unflattend:                        9
% 3.57/0.99  smt_new_axioms:                         0
% 3.57/0.99  pred_elim_cands:                        3
% 3.57/0.99  pred_elim:                              1
% 3.57/0.99  pred_elim_cl:                           1
% 3.57/0.99  pred_elim_cycles:                       3
% 3.57/0.99  merged_defs:                            0
% 3.57/0.99  merged_defs_ncl:                        0
% 3.57/0.99  bin_hyper_res:                          0
% 3.57/0.99  prep_cycles:                            4
% 3.57/0.99  pred_elim_time:                         0.003
% 3.57/0.99  splitting_time:                         0.
% 3.57/0.99  sem_filter_time:                        0.
% 3.57/0.99  monotx_time:                            0.001
% 3.57/0.99  subtype_inf_time:                       0.
% 3.57/0.99  
% 3.57/0.99  ------ Problem properties
% 3.57/0.99  
% 3.57/0.99  clauses:                                24
% 3.57/0.99  conjectures:                            6
% 3.57/0.99  epr:                                    7
% 3.57/0.99  horn:                                   17
% 3.57/0.99  ground:                                 6
% 3.57/0.99  unary:                                  11
% 3.57/0.99  binary:                                 7
% 3.57/0.99  lits:                                   53
% 3.57/0.99  lits_eq:                                29
% 3.57/0.99  fd_pure:                                0
% 3.57/0.99  fd_pseudo:                              0
% 3.57/0.99  fd_cond:                                6
% 3.57/0.99  fd_pseudo_cond:                         0
% 3.57/0.99  ac_symbols:                             0
% 3.57/0.99  
% 3.57/0.99  ------ Propositional Solver
% 3.57/0.99  
% 3.57/0.99  prop_solver_calls:                      29
% 3.57/0.99  prop_fast_solver_calls:                 1097
% 3.57/0.99  smt_solver_calls:                       0
% 3.57/0.99  smt_fast_solver_calls:                  0
% 3.57/0.99  prop_num_of_clauses:                    3935
% 3.57/0.99  prop_preprocess_simplified:             11229
% 3.57/0.99  prop_fo_subsumed:                       78
% 3.57/0.99  prop_solver_time:                       0.
% 3.57/0.99  smt_solver_time:                        0.
% 3.57/0.99  smt_fast_solver_time:                   0.
% 3.57/0.99  prop_fast_solver_time:                  0.
% 3.57/0.99  prop_unsat_core_time:                   0.
% 3.57/0.99  
% 3.57/0.99  ------ QBF
% 3.57/0.99  
% 3.57/0.99  qbf_q_res:                              0
% 3.57/0.99  qbf_num_tautologies:                    0
% 3.57/0.99  qbf_prep_cycles:                        0
% 3.57/0.99  
% 3.57/0.99  ------ BMC1
% 3.57/0.99  
% 3.57/0.99  bmc1_current_bound:                     -1
% 3.57/0.99  bmc1_last_solved_bound:                 -1
% 3.57/0.99  bmc1_unsat_core_size:                   -1
% 3.57/0.99  bmc1_unsat_core_parents_size:           -1
% 3.57/0.99  bmc1_merge_next_fun:                    0
% 3.57/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation
% 3.57/0.99  
% 3.57/0.99  inst_num_of_clauses:                    1444
% 3.57/0.99  inst_num_in_passive:                    644
% 3.57/0.99  inst_num_in_active:                     691
% 3.57/0.99  inst_num_in_unprocessed:                109
% 3.57/0.99  inst_num_of_loops:                      710
% 3.57/0.99  inst_num_of_learning_restarts:          0
% 3.57/0.99  inst_num_moves_active_passive:          17
% 3.57/0.99  inst_lit_activity:                      0
% 3.57/0.99  inst_lit_activity_moves:                0
% 3.57/0.99  inst_num_tautologies:                   0
% 3.57/0.99  inst_num_prop_implied:                  0
% 3.57/0.99  inst_num_existing_simplified:           0
% 3.57/0.99  inst_num_eq_res_simplified:             0
% 3.57/0.99  inst_num_child_elim:                    0
% 3.57/0.99  inst_num_of_dismatching_blockings:      393
% 3.57/0.99  inst_num_of_non_proper_insts:           1063
% 3.57/0.99  inst_num_of_duplicates:                 0
% 3.57/0.99  inst_inst_num_from_inst_to_res:         0
% 3.57/0.99  inst_dismatching_checking_time:         0.
% 3.57/0.99  
% 3.57/0.99  ------ Resolution
% 3.57/0.99  
% 3.57/0.99  res_num_of_clauses:                     0
% 3.57/0.99  res_num_in_passive:                     0
% 3.57/0.99  res_num_in_active:                      0
% 3.57/0.99  res_num_of_loops:                       122
% 3.57/0.99  res_forward_subset_subsumed:            30
% 3.57/0.99  res_backward_subset_subsumed:           0
% 3.57/0.99  res_forward_subsumed:                   0
% 3.57/0.99  res_backward_subsumed:                  0
% 3.57/0.99  res_forward_subsumption_resolution:     0
% 3.57/0.99  res_backward_subsumption_resolution:    0
% 3.57/0.99  res_clause_to_clause_subsumption:       1457
% 3.57/0.99  res_orphan_elimination:                 0
% 3.57/0.99  res_tautology_del:                      19
% 3.57/0.99  res_num_eq_res_simplified:              0
% 3.57/0.99  res_num_sel_changes:                    0
% 3.57/0.99  res_moves_from_active_to_pass:          0
% 3.57/0.99  
% 3.57/0.99  ------ Superposition
% 3.57/0.99  
% 3.57/0.99  sup_time_total:                         0.
% 3.57/0.99  sup_time_generating:                    0.
% 3.57/0.99  sup_time_sim_full:                      0.
% 3.57/0.99  sup_time_sim_immed:                     0.
% 3.57/0.99  
% 3.57/0.99  sup_num_of_clauses:                     135
% 3.57/0.99  sup_num_in_active:                      7
% 3.57/0.99  sup_num_in_passive:                     128
% 3.57/0.99  sup_num_of_loops:                       140
% 3.57/0.99  sup_fw_superposition:                   619
% 3.57/0.99  sup_bw_superposition:                   2402
% 3.57/0.99  sup_immediate_simplified:               1865
% 3.57/0.99  sup_given_eliminated:                   0
% 3.57/0.99  comparisons_done:                       0
% 3.57/0.99  comparisons_avoided:                    93
% 3.57/0.99  
% 3.57/0.99  ------ Simplifications
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  sim_fw_subset_subsumed:                 1405
% 3.57/0.99  sim_bw_subset_subsumed:                 99
% 3.57/0.99  sim_fw_subsumed:                        256
% 3.57/0.99  sim_bw_subsumed:                        8
% 3.57/0.99  sim_fw_subsumption_res:                 1
% 3.57/0.99  sim_bw_subsumption_res:                 0
% 3.57/0.99  sim_tautology_del:                      18
% 3.57/0.99  sim_eq_tautology_del:                   106
% 3.57/0.99  sim_eq_res_simp:                        26
% 3.57/0.99  sim_fw_demodulated:                     123
% 3.57/0.99  sim_bw_demodulated:                     127
% 3.57/0.99  sim_light_normalised:                   81
% 3.57/0.99  sim_joinable_taut:                      0
% 3.57/0.99  sim_joinable_simp:                      0
% 3.57/0.99  sim_ac_normalised:                      0
% 3.57/0.99  sim_smt_subsumption:                    0
% 3.57/0.99  
%------------------------------------------------------------------------------
