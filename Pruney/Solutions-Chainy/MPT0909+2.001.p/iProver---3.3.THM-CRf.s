%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:52 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 812 expanded)
%              Number of clauses        :   91 ( 250 expanded)
%              Number of leaves         :   17 ( 180 expanded)
%              Depth                    :   28
%              Number of atoms          :  503 (3672 expanded)
%              Number of equality atoms :  365 (2430 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f36])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X5 ) ) ) )
         => ( k5_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f30])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k5_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X5
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k5_mcart_1(sK3,sK4,sK5,sK7) != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK6 = X5
                  | k3_mcart_1(X5,X6,X7) != sK7
                  | ~ m1_subset_1(X7,sK5) )
              | ~ m1_subset_1(X6,sK4) )
          | ~ m1_subset_1(X5,sK3) )
      & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK7) != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK6 = X5
                | k3_mcart_1(X5,X6,X7) != sK7
                | ~ m1_subset_1(X7,sK5) )
            | ~ m1_subset_1(X6,sK4) )
        | ~ m1_subset_1(X5,sK3) )
    & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f31,f40])).

fof(f72,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 )
      & ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f38])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f65,f76])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f66,f76])).

fof(f93,plain,(
    ! [X2,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f84])).

fof(f70,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f70,f53])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f67,f76])).

fof(f92,plain,(
    ! [X2,X0,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f83])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f64,f53])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f68,f76])).

fof(f91,plain,(
    ! [X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f82])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X5
      | k3_mcart_1(X5,X6,X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f86,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X5
      | k4_tarski(k4_tarski(X5,X6),X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(definition_unfolding,[],[f71,f52])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f62,f53])).

fof(f75,plain,(
    k5_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_16,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_783,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_790,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2135,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(sK2(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_783,c_790])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_24,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_35,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_23,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_36,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_446,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_848,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_849,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_848])).

cnf(c_882,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_883,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_908,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_909,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_908])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_778,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_789,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2212,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_789])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_261,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_zfmisc_1(X2,X3) != X1
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_262,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_777,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_2256,plain,
    ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2212,c_777])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_796,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2134,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_783,c_796])).

cnf(c_3017,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_2256,c_2134])).

cnf(c_3171,plain,
    ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | m1_subset_1(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3017,c_778])).

cnf(c_22,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_782,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3288,plain,
    ( k7_mcart_1(k2_zfmisc_1(X0,k1_xboole_0),X1,X2,X3) = k2_mcart_1(X3)
    | k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_782])).

cnf(c_6091,plain,
    ( k7_mcart_1(k2_zfmisc_1(X0,k1_xboole_0),X1,X2,sK7) = k2_mcart_1(sK7)
    | k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(superposition,[status(thm)],[c_3171,c_3288])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_788,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3378,plain,
    ( m1_subset_1(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(k7_mcart_1(k2_zfmisc_1(X1,k1_xboole_0),X2,X3,X0),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_788])).

cnf(c_6956,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(k2_mcart_1(sK7),X1) = iProver_top
    | m1_subset_1(sK7,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6091,c_3378])).

cnf(c_7118,plain,
    ( m1_subset_1(k2_mcart_1(sK7),X1) = iProver_top
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6956,c_3171])).

cnf(c_7119,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(k2_mcart_1(sK7),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_7118])).

cnf(c_7124,plain,
    ( k7_mcart_1(X0,X1,X2,k2_mcart_1(sK7)) = k2_mcart_1(k2_mcart_1(sK7))
    | k2_zfmisc_1(X3,k1_xboole_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X4 ),
    inference(superposition,[status(thm)],[c_7119,c_782])).

cnf(c_3162,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_3017,c_24])).

cnf(c_21,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1417,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_21,c_21])).

cnf(c_3173,plain,
    ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3162,c_1417])).

cnf(c_3174,plain,
    ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3173])).

cnf(c_7275,plain,
    ( k1_xboole_0 = X0
    | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7124,c_28,c_27,c_26,c_35,c_36,c_849,c_883,c_909,c_3174])).

cnf(c_7276,plain,
    ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_7275])).

cnf(c_7441,plain,
    ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_7276,c_28])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_786,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2255,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2212,c_786])).

cnf(c_2407,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2255,c_777])).

cnf(c_3013,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
    inference(superposition,[status(thm)],[c_2407,c_2134])).

cnf(c_29,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ m1_subset_1(X1,sK4)
    | ~ m1_subset_1(X2,sK3)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK7
    | sK6 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_779,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
    | sK6 = X0
    | m1_subset_1(X2,sK5) != iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4702,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK7),X0) != sK7
    | k1_mcart_1(k1_mcart_1(sK7)) = sK6
    | m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3013,c_779])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_780,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2051,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_778,c_780])).

cnf(c_2260,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2051,c_28,c_27,c_26,c_35,c_36,c_849,c_883,c_909])).

cnf(c_25,negated_conjecture,
    ( k5_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2262,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) != sK6 ),
    inference(demodulation,[status(thm)],[c_2260,c_25])).

cnf(c_2406,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2255,c_786])).

cnf(c_3014,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2406,c_2134])).

cnf(c_4660,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_790])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_787,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2405,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2255,c_787])).

cnf(c_3015,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2405,c_2134])).

cnf(c_4665,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3015,c_790])).

cnf(c_4707,plain,
    ( k4_tarski(k1_mcart_1(sK7),X0) != sK7
    | k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4702,c_2262,c_4660,c_4665])).

cnf(c_4708,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK7),X0) != sK7
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_4707])).

cnf(c_8229,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7441,c_4708])).

cnf(c_3285,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_778,c_782])).

cnf(c_3672,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3285,c_28,c_27,c_26,c_35,c_36,c_849,c_883,c_909])).

cnf(c_3375,plain,
    ( m1_subset_1(k7_mcart_1(sK3,sK4,sK5,sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_788])).

cnf(c_3674,plain,
    ( m1_subset_1(k2_mcart_1(sK7),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3672,c_3375])).

cnf(c_8410,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8229,c_3674])).

cnf(c_8449,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_8410,c_24])).

cnf(c_8451,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8449,c_1417])).

cnf(c_8452,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8451])).

cnf(c_8691,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2135,c_28,c_27,c_26,c_35,c_36,c_849,c_883,c_909,c_8452])).

cnf(c_8736,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8691,c_26])).

cnf(c_8756,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8736])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.68/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.98  
% 3.68/0.98  ------  iProver source info
% 3.68/0.98  
% 3.68/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.98  git: non_committed_changes: false
% 3.68/0.98  git: last_make_outside_of_git: false
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options
% 3.68/0.98  
% 3.68/0.98  --out_options                           all
% 3.68/0.98  --tptp_safe_out                         true
% 3.68/0.98  --problem_path                          ""
% 3.68/0.98  --include_path                          ""
% 3.68/0.98  --clausifier                            res/vclausify_rel
% 3.68/0.98  --clausifier_options                    ""
% 3.68/0.98  --stdin                                 false
% 3.68/0.98  --stats_out                             all
% 3.68/0.98  
% 3.68/0.98  ------ General Options
% 3.68/0.98  
% 3.68/0.98  --fof                                   false
% 3.68/0.98  --time_out_real                         305.
% 3.68/0.98  --time_out_virtual                      -1.
% 3.68/0.98  --symbol_type_check                     false
% 3.68/0.98  --clausify_out                          false
% 3.68/0.98  --sig_cnt_out                           false
% 3.68/0.98  --trig_cnt_out                          false
% 3.68/0.98  --trig_cnt_out_tolerance                1.
% 3.68/0.98  --trig_cnt_out_sk_spl                   false
% 3.68/0.98  --abstr_cl_out                          false
% 3.68/0.98  
% 3.68/0.98  ------ Global Options
% 3.68/0.98  
% 3.68/0.98  --schedule                              default
% 3.68/0.98  --add_important_lit                     false
% 3.68/0.98  --prop_solver_per_cl                    1000
% 3.68/0.98  --min_unsat_core                        false
% 3.68/0.98  --soft_assumptions                      false
% 3.68/0.98  --soft_lemma_size                       3
% 3.68/0.98  --prop_impl_unit_size                   0
% 3.68/0.98  --prop_impl_unit                        []
% 3.68/0.98  --share_sel_clauses                     true
% 3.68/0.98  --reset_solvers                         false
% 3.68/0.98  --bc_imp_inh                            [conj_cone]
% 3.68/0.98  --conj_cone_tolerance                   3.
% 3.68/0.98  --extra_neg_conj                        none
% 3.68/0.98  --large_theory_mode                     true
% 3.68/0.98  --prolific_symb_bound                   200
% 3.68/0.98  --lt_threshold                          2000
% 3.68/0.98  --clause_weak_htbl                      true
% 3.68/0.98  --gc_record_bc_elim                     false
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing Options
% 3.68/0.98  
% 3.68/0.98  --preprocessing_flag                    true
% 3.68/0.98  --time_out_prep_mult                    0.1
% 3.68/0.98  --splitting_mode                        input
% 3.68/0.98  --splitting_grd                         true
% 3.68/0.98  --splitting_cvd                         false
% 3.68/0.98  --splitting_cvd_svl                     false
% 3.68/0.98  --splitting_nvd                         32
% 3.68/0.98  --sub_typing                            true
% 3.68/0.98  --prep_gs_sim                           true
% 3.68/0.98  --prep_unflatten                        true
% 3.68/0.98  --prep_res_sim                          true
% 3.68/0.98  --prep_upred                            true
% 3.68/0.98  --prep_sem_filter                       exhaustive
% 3.68/0.98  --prep_sem_filter_out                   false
% 3.68/0.98  --pred_elim                             true
% 3.68/0.98  --res_sim_input                         true
% 3.68/0.98  --eq_ax_congr_red                       true
% 3.68/0.98  --pure_diseq_elim                       true
% 3.68/0.98  --brand_transform                       false
% 3.68/0.98  --non_eq_to_eq                          false
% 3.68/0.98  --prep_def_merge                        true
% 3.68/0.98  --prep_def_merge_prop_impl              false
% 3.68/0.98  --prep_def_merge_mbd                    true
% 3.68/0.98  --prep_def_merge_tr_red                 false
% 3.68/0.98  --prep_def_merge_tr_cl                  false
% 3.68/0.98  --smt_preprocessing                     true
% 3.68/0.98  --smt_ac_axioms                         fast
% 3.68/0.98  --preprocessed_out                      false
% 3.68/0.98  --preprocessed_stats                    false
% 3.68/0.98  
% 3.68/0.98  ------ Abstraction refinement Options
% 3.68/0.98  
% 3.68/0.98  --abstr_ref                             []
% 3.68/0.98  --abstr_ref_prep                        false
% 3.68/0.98  --abstr_ref_until_sat                   false
% 3.68/0.98  --abstr_ref_sig_restrict                funpre
% 3.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.98  --abstr_ref_under                       []
% 3.68/0.98  
% 3.68/0.98  ------ SAT Options
% 3.68/0.98  
% 3.68/0.98  --sat_mode                              false
% 3.68/0.98  --sat_fm_restart_options                ""
% 3.68/0.98  --sat_gr_def                            false
% 3.68/0.98  --sat_epr_types                         true
% 3.68/0.98  --sat_non_cyclic_types                  false
% 3.68/0.98  --sat_finite_models                     false
% 3.68/0.98  --sat_fm_lemmas                         false
% 3.68/0.98  --sat_fm_prep                           false
% 3.68/0.98  --sat_fm_uc_incr                        true
% 3.68/0.98  --sat_out_model                         small
% 3.68/0.98  --sat_out_clauses                       false
% 3.68/0.98  
% 3.68/0.98  ------ QBF Options
% 3.68/0.98  
% 3.68/0.98  --qbf_mode                              false
% 3.68/0.98  --qbf_elim_univ                         false
% 3.68/0.98  --qbf_dom_inst                          none
% 3.68/0.98  --qbf_dom_pre_inst                      false
% 3.68/0.98  --qbf_sk_in                             false
% 3.68/0.98  --qbf_pred_elim                         true
% 3.68/0.98  --qbf_split                             512
% 3.68/0.98  
% 3.68/0.98  ------ BMC1 Options
% 3.68/0.98  
% 3.68/0.98  --bmc1_incremental                      false
% 3.68/0.98  --bmc1_axioms                           reachable_all
% 3.68/0.98  --bmc1_min_bound                        0
% 3.68/0.98  --bmc1_max_bound                        -1
% 3.68/0.98  --bmc1_max_bound_default                -1
% 3.68/0.98  --bmc1_symbol_reachability              true
% 3.68/0.98  --bmc1_property_lemmas                  false
% 3.68/0.98  --bmc1_k_induction                      false
% 3.68/0.98  --bmc1_non_equiv_states                 false
% 3.68/0.98  --bmc1_deadlock                         false
% 3.68/0.98  --bmc1_ucm                              false
% 3.68/0.98  --bmc1_add_unsat_core                   none
% 3.68/0.98  --bmc1_unsat_core_children              false
% 3.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.98  --bmc1_out_stat                         full
% 3.68/0.98  --bmc1_ground_init                      false
% 3.68/0.98  --bmc1_pre_inst_next_state              false
% 3.68/0.98  --bmc1_pre_inst_state                   false
% 3.68/0.98  --bmc1_pre_inst_reach_state             false
% 3.68/0.98  --bmc1_out_unsat_core                   false
% 3.68/0.98  --bmc1_aig_witness_out                  false
% 3.68/0.98  --bmc1_verbose                          false
% 3.68/0.98  --bmc1_dump_clauses_tptp                false
% 3.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.98  --bmc1_dump_file                        -
% 3.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.98  --bmc1_ucm_extend_mode                  1
% 3.68/0.98  --bmc1_ucm_init_mode                    2
% 3.68/0.98  --bmc1_ucm_cone_mode                    none
% 3.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.98  --bmc1_ucm_relax_model                  4
% 3.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.98  --bmc1_ucm_layered_model                none
% 3.68/0.98  --bmc1_ucm_max_lemma_size               10
% 3.68/0.98  
% 3.68/0.98  ------ AIG Options
% 3.68/0.98  
% 3.68/0.98  --aig_mode                              false
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation Options
% 3.68/0.98  
% 3.68/0.98  --instantiation_flag                    true
% 3.68/0.98  --inst_sos_flag                         true
% 3.68/0.98  --inst_sos_phase                        true
% 3.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel_side                     num_symb
% 3.68/0.98  --inst_solver_per_active                1400
% 3.68/0.98  --inst_solver_calls_frac                1.
% 3.68/0.98  --inst_passive_queue_type               priority_queues
% 3.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.98  --inst_passive_queues_freq              [25;2]
% 3.68/0.98  --inst_dismatching                      true
% 3.68/0.98  --inst_eager_unprocessed_to_passive     true
% 3.68/0.98  --inst_prop_sim_given                   true
% 3.68/0.98  --inst_prop_sim_new                     false
% 3.68/0.98  --inst_subs_new                         false
% 3.68/0.98  --inst_eq_res_simp                      false
% 3.68/0.98  --inst_subs_given                       false
% 3.68/0.98  --inst_orphan_elimination               true
% 3.68/0.98  --inst_learning_loop_flag               true
% 3.68/0.98  --inst_learning_start                   3000
% 3.68/0.98  --inst_learning_factor                  2
% 3.68/0.98  --inst_start_prop_sim_after_learn       3
% 3.68/0.98  --inst_sel_renew                        solver
% 3.68/0.98  --inst_lit_activity_flag                true
% 3.68/0.98  --inst_restr_to_given                   false
% 3.68/0.98  --inst_activity_threshold               500
% 3.68/0.98  --inst_out_proof                        true
% 3.68/0.98  
% 3.68/0.98  ------ Resolution Options
% 3.68/0.98  
% 3.68/0.98  --resolution_flag                       true
% 3.68/0.98  --res_lit_sel                           adaptive
% 3.68/0.98  --res_lit_sel_side                      none
% 3.68/0.98  --res_ordering                          kbo
% 3.68/0.98  --res_to_prop_solver                    active
% 3.68/0.98  --res_prop_simpl_new                    false
% 3.68/0.98  --res_prop_simpl_given                  true
% 3.68/0.98  --res_passive_queue_type                priority_queues
% 3.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.98  --res_passive_queues_freq               [15;5]
% 3.68/0.98  --res_forward_subs                      full
% 3.68/0.98  --res_backward_subs                     full
% 3.68/0.98  --res_forward_subs_resolution           true
% 3.68/0.98  --res_backward_subs_resolution          true
% 3.68/0.98  --res_orphan_elimination                true
% 3.68/0.98  --res_time_limit                        2.
% 3.68/0.98  --res_out_proof                         true
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Options
% 3.68/0.98  
% 3.68/0.98  --superposition_flag                    true
% 3.68/0.98  --sup_passive_queue_type                priority_queues
% 3.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.98  --demod_completeness_check              fast
% 3.68/0.98  --demod_use_ground                      true
% 3.68/0.98  --sup_to_prop_solver                    passive
% 3.68/0.98  --sup_prop_simpl_new                    true
% 3.68/0.98  --sup_prop_simpl_given                  true
% 3.68/0.98  --sup_fun_splitting                     true
% 3.68/0.98  --sup_smt_interval                      50000
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Simplification Setup
% 3.68/0.98  
% 3.68/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.98  --sup_immed_triv                        [TrivRules]
% 3.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_bw_main                     []
% 3.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_input_bw                          []
% 3.68/0.98  
% 3.68/0.98  ------ Combination Options
% 3.68/0.98  
% 3.68/0.98  --comb_res_mult                         3
% 3.68/0.98  --comb_sup_mult                         2
% 3.68/0.98  --comb_inst_mult                        10
% 3.68/0.98  
% 3.68/0.98  ------ Debug Options
% 3.68/0.98  
% 3.68/0.98  --dbg_backtrace                         false
% 3.68/0.98  --dbg_dump_prop_clauses                 false
% 3.68/0.98  --dbg_dump_prop_clauses_file            -
% 3.68/0.98  --dbg_out_stat                          false
% 3.68/0.98  ------ Parsing...
% 3.68/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  ------ Proving...
% 3.68/0.98  ------ Problem Properties 
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  clauses                                 29
% 3.68/0.98  conjectures                             6
% 3.68/0.98  EPR                                     8
% 3.68/0.98  Horn                                    23
% 3.68/0.98  unary                                   10
% 3.68/0.98  binary                                  7
% 3.68/0.98  lits                                    70
% 3.68/0.98  lits eq                                 35
% 3.68/0.98  fd_pure                                 0
% 3.68/0.98  fd_pseudo                               0
% 3.68/0.98  fd_cond                                 8
% 3.68/0.98  fd_pseudo_cond                          1
% 3.68/0.98  AC symbols                              0
% 3.68/0.98  
% 3.68/0.98  ------ Schedule dynamic 5 is on 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  Current options:
% 3.68/0.98  ------ 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options
% 3.68/0.98  
% 3.68/0.98  --out_options                           all
% 3.68/0.98  --tptp_safe_out                         true
% 3.68/0.98  --problem_path                          ""
% 3.68/0.98  --include_path                          ""
% 3.68/0.98  --clausifier                            res/vclausify_rel
% 3.68/0.98  --clausifier_options                    ""
% 3.68/0.98  --stdin                                 false
% 3.68/0.98  --stats_out                             all
% 3.68/0.98  
% 3.68/0.98  ------ General Options
% 3.68/0.98  
% 3.68/0.98  --fof                                   false
% 3.68/0.98  --time_out_real                         305.
% 3.68/0.98  --time_out_virtual                      -1.
% 3.68/0.98  --symbol_type_check                     false
% 3.68/0.98  --clausify_out                          false
% 3.68/0.98  --sig_cnt_out                           false
% 3.68/0.98  --trig_cnt_out                          false
% 3.68/0.98  --trig_cnt_out_tolerance                1.
% 3.68/0.98  --trig_cnt_out_sk_spl                   false
% 3.68/0.98  --abstr_cl_out                          false
% 3.68/0.98  
% 3.68/0.98  ------ Global Options
% 3.68/0.98  
% 3.68/0.98  --schedule                              default
% 3.68/0.98  --add_important_lit                     false
% 3.68/0.98  --prop_solver_per_cl                    1000
% 3.68/0.98  --min_unsat_core                        false
% 3.68/0.98  --soft_assumptions                      false
% 3.68/0.98  --soft_lemma_size                       3
% 3.68/0.98  --prop_impl_unit_size                   0
% 3.68/0.98  --prop_impl_unit                        []
% 3.68/0.98  --share_sel_clauses                     true
% 3.68/0.98  --reset_solvers                         false
% 3.68/0.98  --bc_imp_inh                            [conj_cone]
% 3.68/0.98  --conj_cone_tolerance                   3.
% 3.68/0.98  --extra_neg_conj                        none
% 3.68/0.98  --large_theory_mode                     true
% 3.68/0.98  --prolific_symb_bound                   200
% 3.68/0.98  --lt_threshold                          2000
% 3.68/0.98  --clause_weak_htbl                      true
% 3.68/0.98  --gc_record_bc_elim                     false
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing Options
% 3.68/0.98  
% 3.68/0.98  --preprocessing_flag                    true
% 3.68/0.98  --time_out_prep_mult                    0.1
% 3.68/0.98  --splitting_mode                        input
% 3.68/0.98  --splitting_grd                         true
% 3.68/0.98  --splitting_cvd                         false
% 3.68/0.98  --splitting_cvd_svl                     false
% 3.68/0.98  --splitting_nvd                         32
% 3.68/0.98  --sub_typing                            true
% 3.68/0.98  --prep_gs_sim                           true
% 3.68/0.98  --prep_unflatten                        true
% 3.68/0.98  --prep_res_sim                          true
% 3.68/0.98  --prep_upred                            true
% 3.68/0.98  --prep_sem_filter                       exhaustive
% 3.68/0.98  --prep_sem_filter_out                   false
% 3.68/0.98  --pred_elim                             true
% 3.68/0.98  --res_sim_input                         true
% 3.68/0.98  --eq_ax_congr_red                       true
% 3.68/0.98  --pure_diseq_elim                       true
% 3.68/0.98  --brand_transform                       false
% 3.68/0.98  --non_eq_to_eq                          false
% 3.68/0.98  --prep_def_merge                        true
% 3.68/0.98  --prep_def_merge_prop_impl              false
% 3.68/0.98  --prep_def_merge_mbd                    true
% 3.68/0.98  --prep_def_merge_tr_red                 false
% 3.68/0.98  --prep_def_merge_tr_cl                  false
% 3.68/0.98  --smt_preprocessing                     true
% 3.68/0.98  --smt_ac_axioms                         fast
% 3.68/0.98  --preprocessed_out                      false
% 3.68/0.98  --preprocessed_stats                    false
% 3.68/0.98  
% 3.68/0.98  ------ Abstraction refinement Options
% 3.68/0.98  
% 3.68/0.98  --abstr_ref                             []
% 3.68/0.98  --abstr_ref_prep                        false
% 3.68/0.98  --abstr_ref_until_sat                   false
% 3.68/0.98  --abstr_ref_sig_restrict                funpre
% 3.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.98  --abstr_ref_under                       []
% 3.68/0.98  
% 3.68/0.98  ------ SAT Options
% 3.68/0.98  
% 3.68/0.98  --sat_mode                              false
% 3.68/0.98  --sat_fm_restart_options                ""
% 3.68/0.98  --sat_gr_def                            false
% 3.68/0.98  --sat_epr_types                         true
% 3.68/0.98  --sat_non_cyclic_types                  false
% 3.68/0.98  --sat_finite_models                     false
% 3.68/0.98  --sat_fm_lemmas                         false
% 3.68/0.98  --sat_fm_prep                           false
% 3.68/0.98  --sat_fm_uc_incr                        true
% 3.68/0.98  --sat_out_model                         small
% 3.68/0.98  --sat_out_clauses                       false
% 3.68/0.98  
% 3.68/0.98  ------ QBF Options
% 3.68/0.98  
% 3.68/0.98  --qbf_mode                              false
% 3.68/0.98  --qbf_elim_univ                         false
% 3.68/0.98  --qbf_dom_inst                          none
% 3.68/0.98  --qbf_dom_pre_inst                      false
% 3.68/0.98  --qbf_sk_in                             false
% 3.68/0.98  --qbf_pred_elim                         true
% 3.68/0.98  --qbf_split                             512
% 3.68/0.98  
% 3.68/0.98  ------ BMC1 Options
% 3.68/0.98  
% 3.68/0.98  --bmc1_incremental                      false
% 3.68/0.98  --bmc1_axioms                           reachable_all
% 3.68/0.98  --bmc1_min_bound                        0
% 3.68/0.98  --bmc1_max_bound                        -1
% 3.68/0.98  --bmc1_max_bound_default                -1
% 3.68/0.98  --bmc1_symbol_reachability              true
% 3.68/0.98  --bmc1_property_lemmas                  false
% 3.68/0.98  --bmc1_k_induction                      false
% 3.68/0.98  --bmc1_non_equiv_states                 false
% 3.68/0.98  --bmc1_deadlock                         false
% 3.68/0.98  --bmc1_ucm                              false
% 3.68/0.98  --bmc1_add_unsat_core                   none
% 3.68/0.98  --bmc1_unsat_core_children              false
% 3.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.98  --bmc1_out_stat                         full
% 3.68/0.98  --bmc1_ground_init                      false
% 3.68/0.98  --bmc1_pre_inst_next_state              false
% 3.68/0.98  --bmc1_pre_inst_state                   false
% 3.68/0.98  --bmc1_pre_inst_reach_state             false
% 3.68/0.98  --bmc1_out_unsat_core                   false
% 3.68/0.98  --bmc1_aig_witness_out                  false
% 3.68/0.98  --bmc1_verbose                          false
% 3.68/0.98  --bmc1_dump_clauses_tptp                false
% 3.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.98  --bmc1_dump_file                        -
% 3.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.98  --bmc1_ucm_extend_mode                  1
% 3.68/0.98  --bmc1_ucm_init_mode                    2
% 3.68/0.98  --bmc1_ucm_cone_mode                    none
% 3.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.98  --bmc1_ucm_relax_model                  4
% 3.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.98  --bmc1_ucm_layered_model                none
% 3.68/0.98  --bmc1_ucm_max_lemma_size               10
% 3.68/0.98  
% 3.68/0.98  ------ AIG Options
% 3.68/0.98  
% 3.68/0.98  --aig_mode                              false
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation Options
% 3.68/0.98  
% 3.68/0.98  --instantiation_flag                    true
% 3.68/0.98  --inst_sos_flag                         true
% 3.68/0.98  --inst_sos_phase                        true
% 3.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel_side                     none
% 3.68/0.98  --inst_solver_per_active                1400
% 3.68/0.98  --inst_solver_calls_frac                1.
% 3.68/0.98  --inst_passive_queue_type               priority_queues
% 3.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.98  --inst_passive_queues_freq              [25;2]
% 3.68/0.98  --inst_dismatching                      true
% 3.68/0.98  --inst_eager_unprocessed_to_passive     true
% 3.68/0.98  --inst_prop_sim_given                   true
% 3.68/0.98  --inst_prop_sim_new                     false
% 3.68/0.98  --inst_subs_new                         false
% 3.68/0.98  --inst_eq_res_simp                      false
% 3.68/0.98  --inst_subs_given                       false
% 3.68/0.98  --inst_orphan_elimination               true
% 3.68/0.98  --inst_learning_loop_flag               true
% 3.68/0.98  --inst_learning_start                   3000
% 3.68/0.98  --inst_learning_factor                  2
% 3.68/0.98  --inst_start_prop_sim_after_learn       3
% 3.68/0.98  --inst_sel_renew                        solver
% 3.68/0.98  --inst_lit_activity_flag                true
% 3.68/0.98  --inst_restr_to_given                   false
% 3.68/0.98  --inst_activity_threshold               500
% 3.68/0.98  --inst_out_proof                        true
% 3.68/0.98  
% 3.68/0.98  ------ Resolution Options
% 3.68/0.98  
% 3.68/0.98  --resolution_flag                       false
% 3.68/0.98  --res_lit_sel                           adaptive
% 3.68/0.98  --res_lit_sel_side                      none
% 3.68/0.98  --res_ordering                          kbo
% 3.68/0.98  --res_to_prop_solver                    active
% 3.68/0.98  --res_prop_simpl_new                    false
% 3.68/0.98  --res_prop_simpl_given                  true
% 3.68/0.98  --res_passive_queue_type                priority_queues
% 3.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.98  --res_passive_queues_freq               [15;5]
% 3.68/0.98  --res_forward_subs                      full
% 3.68/0.98  --res_backward_subs                     full
% 3.68/0.98  --res_forward_subs_resolution           true
% 3.68/0.98  --res_backward_subs_resolution          true
% 3.68/0.98  --res_orphan_elimination                true
% 3.68/0.98  --res_time_limit                        2.
% 3.68/0.98  --res_out_proof                         true
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Options
% 3.68/0.98  
% 3.68/0.98  --superposition_flag                    true
% 3.68/0.98  --sup_passive_queue_type                priority_queues
% 3.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.98  --demod_completeness_check              fast
% 3.68/0.98  --demod_use_ground                      true
% 3.68/0.98  --sup_to_prop_solver                    passive
% 3.68/0.98  --sup_prop_simpl_new                    true
% 3.68/0.98  --sup_prop_simpl_given                  true
% 3.68/0.98  --sup_fun_splitting                     true
% 3.68/0.98  --sup_smt_interval                      50000
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Simplification Setup
% 3.68/0.98  
% 3.68/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.98  --sup_immed_triv                        [TrivRules]
% 3.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_bw_main                     []
% 3.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_input_bw                          []
% 3.68/0.98  
% 3.68/0.98  ------ Combination Options
% 3.68/0.98  
% 3.68/0.98  --comb_res_mult                         3
% 3.68/0.98  --comb_sup_mult                         2
% 3.68/0.98  --comb_inst_mult                        10
% 3.68/0.98  
% 3.68/0.98  ------ Debug Options
% 3.68/0.98  
% 3.68/0.98  --dbg_backtrace                         false
% 3.68/0.98  --dbg_dump_prop_clauses                 false
% 3.68/0.98  --dbg_dump_prop_clauses_file            -
% 3.68/0.98  --dbg_out_stat                          false
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  % SZS status Theorem for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98   Resolution empty clause
% 3.68/0.98  
% 3.68/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  fof(f13,axiom,(
% 3.68/0.98    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f28,plain,(
% 3.68/0.98    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.68/0.98    inference(ennf_transformation,[],[f13])).
% 3.68/0.98  
% 3.68/0.98  fof(f36,plain,(
% 3.68/0.98    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f37,plain,(
% 3.68/0.98    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f36])).
% 3.68/0.98  
% 3.68/0.98  fof(f59,plain,(
% 3.68/0.98    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.68/0.98    inference(cnf_transformation,[],[f37])).
% 3.68/0.98  
% 3.68/0.98  fof(f4,axiom,(
% 3.68/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f21,plain,(
% 3.68/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.68/0.98    inference(ennf_transformation,[],[f4])).
% 3.68/0.98  
% 3.68/0.98  fof(f49,plain,(
% 3.68/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f21])).
% 3.68/0.98  
% 3.68/0.98  fof(f16,conjecture,(
% 3.68/0.98    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f17,negated_conjecture,(
% 3.68/0.98    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.68/0.98    inference(negated_conjecture,[],[f16])).
% 3.68/0.98  
% 3.68/0.98  fof(f30,plain,(
% 3.68/0.98    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.68/0.98    inference(ennf_transformation,[],[f17])).
% 3.68/0.98  
% 3.68/0.98  fof(f31,plain,(
% 3.68/0.98    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.68/0.98    inference(flattening,[],[f30])).
% 3.68/0.98  
% 3.68/0.98  fof(f40,plain,(
% 3.68/0.98    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k5_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X5 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f41,plain,(
% 3.68/0.98    k5_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X5 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f31,f40])).
% 3.68/0.98  
% 3.68/0.98  fof(f72,plain,(
% 3.68/0.98    k1_xboole_0 != sK3),
% 3.68/0.98    inference(cnf_transformation,[],[f41])).
% 3.68/0.98  
% 3.68/0.98  fof(f73,plain,(
% 3.68/0.98    k1_xboole_0 != sK4),
% 3.68/0.98    inference(cnf_transformation,[],[f41])).
% 3.68/0.98  
% 3.68/0.98  fof(f74,plain,(
% 3.68/0.98    k1_xboole_0 != sK5),
% 3.68/0.98    inference(cnf_transformation,[],[f41])).
% 3.68/0.98  
% 3.68/0.98  fof(f15,axiom,(
% 3.68/0.98    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f38,plain,(
% 3.68/0.98    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.68/0.98    inference(nnf_transformation,[],[f15])).
% 3.68/0.98  
% 3.68/0.98  fof(f39,plain,(
% 3.68/0.98    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.68/0.98    inference(flattening,[],[f38])).
% 3.68/0.98  
% 3.68/0.98  fof(f65,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.68/0.98    inference(cnf_transformation,[],[f39])).
% 3.68/0.98  
% 3.68/0.98  fof(f9,axiom,(
% 3.68/0.98    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f54,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f9])).
% 3.68/0.98  
% 3.68/0.98  fof(f8,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f53,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f8])).
% 3.68/0.98  
% 3.68/0.98  fof(f76,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.68/0.98    inference(definition_unfolding,[],[f54,f53])).
% 3.68/0.98  
% 3.68/0.98  fof(f85,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.68/0.98    inference(definition_unfolding,[],[f65,f76])).
% 3.68/0.98  
% 3.68/0.98  fof(f66,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 3.68/0.98    inference(cnf_transformation,[],[f39])).
% 3.68/0.98  
% 3.68/0.98  fof(f84,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 3.68/0.98    inference(definition_unfolding,[],[f66,f76])).
% 3.68/0.98  
% 3.68/0.98  fof(f93,plain,(
% 3.68/0.98    ( ! [X2,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0) )),
% 3.68/0.98    inference(equality_resolution,[],[f84])).
% 3.68/0.98  
% 3.68/0.98  fof(f70,plain,(
% 3.68/0.98    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 3.68/0.98    inference(cnf_transformation,[],[f41])).
% 3.68/0.98  
% 3.68/0.98  fof(f87,plain,(
% 3.68/0.98    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 3.68/0.98    inference(definition_unfolding,[],[f70,f53])).
% 3.68/0.98  
% 3.68/0.98  fof(f5,axiom,(
% 3.68/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f22,plain,(
% 3.68/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.68/0.98    inference(ennf_transformation,[],[f5])).
% 3.68/0.98  
% 3.68/0.98  fof(f23,plain,(
% 3.68/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.68/0.98    inference(flattening,[],[f22])).
% 3.68/0.98  
% 3.68/0.98  fof(f50,plain,(
% 3.68/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f23])).
% 3.68/0.98  
% 3.68/0.98  fof(f6,axiom,(
% 3.68/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f51,plain,(
% 3.68/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f6])).
% 3.68/0.98  
% 3.68/0.98  fof(f12,axiom,(
% 3.68/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f26,plain,(
% 3.68/0.98    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 3.68/0.98    inference(ennf_transformation,[],[f12])).
% 3.68/0.98  
% 3.68/0.98  fof(f27,plain,(
% 3.68/0.98    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 3.68/0.98    inference(flattening,[],[f26])).
% 3.68/0.98  
% 3.68/0.98  fof(f58,plain,(
% 3.68/0.98    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f27])).
% 3.68/0.98  
% 3.68/0.98  fof(f1,axiom,(
% 3.68/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f18,plain,(
% 3.68/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.68/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 3.68/0.98  
% 3.68/0.98  fof(f19,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f18])).
% 3.68/0.98  
% 3.68/0.98  fof(f42,plain,(
% 3.68/0.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f19])).
% 3.68/0.98  
% 3.68/0.98  fof(f67,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 3.68/0.98    inference(cnf_transformation,[],[f39])).
% 3.68/0.98  
% 3.68/0.98  fof(f83,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 3.68/0.98    inference(definition_unfolding,[],[f67,f76])).
% 3.68/0.98  
% 3.68/0.98  fof(f92,plain,(
% 3.68/0.98    ( ! [X2,X0,X3] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3) = k1_xboole_0) )),
% 3.68/0.98    inference(equality_resolution,[],[f83])).
% 3.68/0.98  
% 3.68/0.98  fof(f14,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f29,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.68/0.98    inference(ennf_transformation,[],[f14])).
% 3.68/0.98  
% 3.68/0.98  fof(f64,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.68/0.98    inference(cnf_transformation,[],[f29])).
% 3.68/0.98  
% 3.68/0.98  fof(f78,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.68/0.98    inference(definition_unfolding,[],[f64,f53])).
% 3.68/0.98  
% 3.68/0.98  fof(f10,axiom,(
% 3.68/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f24,plain,(
% 3.68/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.68/0.98    inference(ennf_transformation,[],[f10])).
% 3.68/0.98  
% 3.68/0.98  fof(f55,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f24])).
% 3.68/0.98  
% 3.68/0.98  fof(f77,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.68/0.98    inference(definition_unfolding,[],[f55,f53])).
% 3.68/0.98  
% 3.68/0.98  fof(f68,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 3.68/0.98    inference(cnf_transformation,[],[f39])).
% 3.68/0.98  
% 3.68/0.98  fof(f82,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 3.68/0.98    inference(definition_unfolding,[],[f68,f76])).
% 3.68/0.98  
% 3.68/0.98  fof(f91,plain,(
% 3.68/0.98    ( ! [X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) = k1_xboole_0) )),
% 3.68/0.98    inference(equality_resolution,[],[f82])).
% 3.68/0.98  
% 3.68/0.98  fof(f11,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f25,plain,(
% 3.68/0.98    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.68/0.98    inference(ennf_transformation,[],[f11])).
% 3.68/0.98  
% 3.68/0.98  fof(f56,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f25])).
% 3.68/0.98  
% 3.68/0.98  fof(f71,plain,(
% 3.68/0.98    ( ! [X6,X7,X5] : (sK6 = X5 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f41])).
% 3.68/0.98  
% 3.68/0.98  fof(f7,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f52,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f7])).
% 3.68/0.98  
% 3.68/0.98  fof(f86,plain,(
% 3.68/0.98    ( ! [X6,X7,X5] : (sK6 = X5 | k4_tarski(k4_tarski(X5,X6),X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 3.68/0.98    inference(definition_unfolding,[],[f71,f52])).
% 3.68/0.98  
% 3.68/0.98  fof(f62,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.68/0.98    inference(cnf_transformation,[],[f29])).
% 3.68/0.98  
% 3.68/0.98  fof(f80,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.68/0.98    inference(definition_unfolding,[],[f62,f53])).
% 3.68/0.98  
% 3.68/0.98  fof(f75,plain,(
% 3.68/0.98    k5_mcart_1(sK3,sK4,sK5,sK7) != sK6),
% 3.68/0.98    inference(cnf_transformation,[],[f41])).
% 3.68/0.98  
% 3.68/0.98  fof(f57,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f25])).
% 3.68/0.98  
% 3.68/0.98  cnf(c_16,plain,
% 3.68/0.98      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_783,plain,
% 3.68/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7,plain,
% 3.68/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_790,plain,
% 3.68/0.98      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2135,plain,
% 3.68/0.98      ( k1_xboole_0 = X0 | m1_subset_1(sK2(X0),X0) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_783,c_790]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_28,negated_conjecture,
% 3.68/0.98      ( k1_xboole_0 != sK3 ),
% 3.68/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_27,negated_conjecture,
% 3.68/0.98      ( k1_xboole_0 != sK4 ),
% 3.68/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_26,negated_conjecture,
% 3.68/0.98      ( k1_xboole_0 != sK5 ),
% 3.68/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_24,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = X0
% 3.68/0.98      | k1_xboole_0 = X1
% 3.68/0.98      | k1_xboole_0 = X2
% 3.68/0.98      | k1_xboole_0 = X3 ),
% 3.68/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_35,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_24]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_23,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_36,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_446,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_848,plain,
% 3.68/0.98      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_446]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_849,plain,
% 3.68/0.98      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_848]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_882,plain,
% 3.68/0.98      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_446]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_883,plain,
% 3.68/0.98      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_882]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_908,plain,
% 3.68/0.98      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_446]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_909,plain,
% 3.68/0.98      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_908]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_30,negated_conjecture,
% 3.68/0.98      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_778,plain,
% 3.68/0.98      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_789,plain,
% 3.68/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.68/0.98      | r2_hidden(X0,X1) = iProver_top
% 3.68/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2212,plain,
% 3.68/0.98      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top
% 3.68/0.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_778,c_789]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_9,plain,
% 3.68/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_13,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,X1)
% 3.68/0.98      | ~ v1_relat_1(X1)
% 3.68/0.98      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_261,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,X1)
% 3.68/0.98      | k2_zfmisc_1(X2,X3) != X1
% 3.68/0.98      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_262,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.68/0.98      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_261]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_777,plain,
% 3.68/0.98      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.68/0.98      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2256,plain,
% 3.68/0.98      ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
% 3.68/0.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2212,c_777]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_0,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_796,plain,
% 3.68/0.98      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2134,plain,
% 3.68/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_783,c_796]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3017,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.68/0.98      | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2256,c_2134]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3171,plain,
% 3.68/0.98      ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
% 3.68/0.98      | m1_subset_1(sK7,k1_xboole_0) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_3017,c_778]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_22,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1),X2) = k1_xboole_0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_17,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.68/0.98      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.68/0.98      | k1_xboole_0 = X1
% 3.68/0.98      | k1_xboole_0 = X2
% 3.68/0.98      | k1_xboole_0 = X3 ),
% 3.68/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_782,plain,
% 3.68/0.98      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.68/0.98      | k1_xboole_0 = X0
% 3.68/0.98      | k1_xboole_0 = X1
% 3.68/0.98      | k1_xboole_0 = X2
% 3.68/0.98      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3288,plain,
% 3.68/0.98      ( k7_mcart_1(k2_zfmisc_1(X0,k1_xboole_0),X1,X2,X3) = k2_mcart_1(X3)
% 3.68/0.98      | k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = X1
% 3.68/0.98      | k1_xboole_0 = X2
% 3.68/0.98      | m1_subset_1(X3,k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_22,c_782]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6091,plain,
% 3.68/0.98      ( k7_mcart_1(k2_zfmisc_1(X0,k1_xboole_0),X1,X2,sK7) = k2_mcart_1(sK7)
% 3.68/0.98      | k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
% 3.68/0.98      | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
% 3.68/0.98      | k1_xboole_0 = X1
% 3.68/0.98      | k1_xboole_0 = X2 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_3171,c_3288]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_10,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.68/0.98      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
% 3.68/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_788,plain,
% 3.68/0.98      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.68/0.98      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3378,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_xboole_0) != iProver_top
% 3.68/0.98      | m1_subset_1(k7_mcart_1(k2_zfmisc_1(X1,k1_xboole_0),X2,X3,X0),X3) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_22,c_788]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6956,plain,
% 3.68/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
% 3.68/0.98      | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
% 3.68/0.98      | k1_xboole_0 = X1
% 3.68/0.98      | k1_xboole_0 = X2
% 3.68/0.98      | m1_subset_1(k2_mcart_1(sK7),X1) = iProver_top
% 3.68/0.98      | m1_subset_1(sK7,k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_6091,c_3378]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7118,plain,
% 3.68/0.98      ( m1_subset_1(k2_mcart_1(sK7),X1) = iProver_top
% 3.68/0.98      | k1_xboole_0 = X2
% 3.68/0.98      | k1_xboole_0 = X1
% 3.68/0.98      | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
% 3.68/0.98      | k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.68/0.98      inference(global_propositional_subsumption,[status(thm)],[c_6956,c_3171]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7119,plain,
% 3.68/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
% 3.68/0.98      | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
% 3.68/0.98      | k1_xboole_0 = X1
% 3.68/0.98      | k1_xboole_0 = X2
% 3.68/0.98      | m1_subset_1(k2_mcart_1(sK7),X1) = iProver_top ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_7118]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7124,plain,
% 3.68/0.98      ( k7_mcart_1(X0,X1,X2,k2_mcart_1(sK7)) = k2_mcart_1(k2_mcart_1(sK7))
% 3.68/0.98      | k2_zfmisc_1(X3,k1_xboole_0) = k1_xboole_0
% 3.68/0.98      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 3.68/0.98      | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
% 3.68/0.98      | k1_xboole_0 = X0
% 3.68/0.98      | k1_xboole_0 = X1
% 3.68/0.98      | k1_xboole_0 = X2
% 3.68/0.98      | k1_xboole_0 = X4 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_7119,c_782]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3162,plain,
% 3.68/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 3.68/0.98      | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
% 3.68/0.98      | sK5 = k1_xboole_0
% 3.68/0.98      | sK4 = k1_xboole_0
% 3.68/0.98      | sK3 = k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = X0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_3017,c_24]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_21,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1417,plain,
% 3.68/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_21,c_21]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3173,plain,
% 3.68/0.98      ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
% 3.68/0.98      | sK5 = k1_xboole_0
% 3.68/0.98      | sK4 = k1_xboole_0
% 3.68/0.98      | sK3 = k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = X0
% 3.68/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_3162,c_1417]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3174,plain,
% 3.68/0.98      ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7
% 3.68/0.98      | sK5 = k1_xboole_0
% 3.68/0.98      | sK4 = k1_xboole_0
% 3.68/0.98      | sK3 = k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = X0 ),
% 3.68/0.98      inference(equality_resolution_simp,[status(thm)],[c_3173]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7275,plain,
% 3.68/0.98      ( k1_xboole_0 = X0 | k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7 ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_7124,c_28,c_27,c_26,c_35,c_36,c_849,c_883,c_909,c_3174]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7276,plain,
% 3.68/0.98      ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7 | k1_xboole_0 = X0 ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_7275]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7441,plain,
% 3.68/0.98      ( k4_tarski(k1_mcart_1(sK7),k2_mcart_1(sK7)) = sK7 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_7276,c_28]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_786,plain,
% 3.68/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.68/0.98      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2255,plain,
% 3.68/0.98      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) = iProver_top
% 3.68/0.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2212,c_786]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2407,plain,
% 3.68/0.98      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
% 3.68/0.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2255,c_777]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3013,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.68/0.98      | k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2407,c_2134]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_29,negated_conjecture,
% 3.68/0.98      ( ~ m1_subset_1(X0,sK5)
% 3.68/0.98      | ~ m1_subset_1(X1,sK4)
% 3.68/0.98      | ~ m1_subset_1(X2,sK3)
% 3.68/0.98      | k4_tarski(k4_tarski(X2,X1),X0) != sK7
% 3.68/0.98      | sK6 = X2 ),
% 3.68/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_779,plain,
% 3.68/0.98      ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
% 3.68/0.98      | sK6 = X0
% 3.68/0.98      | m1_subset_1(X2,sK5) != iProver_top
% 3.68/0.98      | m1_subset_1(X1,sK4) != iProver_top
% 3.68/0.98      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4702,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.68/0.98      | k4_tarski(k1_mcart_1(sK7),X0) != sK7
% 3.68/0.98      | k1_mcart_1(k1_mcart_1(sK7)) = sK6
% 3.68/0.98      | m1_subset_1(X0,sK5) != iProver_top
% 3.68/0.98      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) != iProver_top
% 3.68/0.98      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_3013,c_779]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_19,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.68/0.98      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.68/0.98      | k1_xboole_0 = X1
% 3.68/0.98      | k1_xboole_0 = X2
% 3.68/0.98      | k1_xboole_0 = X3 ),
% 3.68/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_780,plain,
% 3.68/0.98      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.68/0.98      | k1_xboole_0 = X0
% 3.68/0.98      | k1_xboole_0 = X1
% 3.68/0.98      | k1_xboole_0 = X2
% 3.68/0.98      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2051,plain,
% 3.68/0.98      ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 3.68/0.98      | sK5 = k1_xboole_0
% 3.68/0.98      | sK4 = k1_xboole_0
% 3.68/0.98      | sK3 = k1_xboole_0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_778,c_780]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2260,plain,
% 3.68/0.98      ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_2051,c_28,c_27,c_26,c_35,c_36,c_849,c_883,c_909]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_25,negated_conjecture,
% 3.68/0.98      ( k5_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
% 3.68/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2262,plain,
% 3.68/0.98      ( k1_mcart_1(k1_mcart_1(sK7)) != sK6 ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_2260,c_25]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2406,plain,
% 3.68/0.98      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top
% 3.68/0.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2255,c_786]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3014,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.68/0.98      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2406,c_2134]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4660,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.68/0.98      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_3014,c_790]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_11,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.68/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_787,plain,
% 3.68/0.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.68/0.98      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2405,plain,
% 3.68/0.98      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
% 3.68/0.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2255,c_787]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3015,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.68/0.98      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2405,c_2134]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4665,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.68/0.98      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_3015,c_790]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4707,plain,
% 3.68/0.98      ( k4_tarski(k1_mcart_1(sK7),X0) != sK7
% 3.68/0.98      | k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.68/0.98      | m1_subset_1(X0,sK5) != iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_4702,c_2262,c_4660,c_4665]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4708,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.68/0.98      | k4_tarski(k1_mcart_1(sK7),X0) != sK7
% 3.68/0.98      | m1_subset_1(X0,sK5) != iProver_top ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_4707]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8229,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.68/0.98      | m1_subset_1(k2_mcart_1(sK7),sK5) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_7441,c_4708]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3285,plain,
% 3.68/0.98      ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7)
% 3.68/0.98      | sK5 = k1_xboole_0
% 3.68/0.98      | sK4 = k1_xboole_0
% 3.68/0.98      | sK3 = k1_xboole_0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_778,c_782]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3672,plain,
% 3.68/0.98      ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_3285,c_28,c_27,c_26,c_35,c_36,c_849,c_883,c_909]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3375,plain,
% 3.68/0.98      ( m1_subset_1(k7_mcart_1(sK3,sK4,sK5,sK7),sK5) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_778,c_788]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3674,plain,
% 3.68/0.98      ( m1_subset_1(k2_mcart_1(sK7),sK5) = iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_3672,c_3375]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8410,plain,
% 3.68/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0 ),
% 3.68/0.98      inference(global_propositional_subsumption,[status(thm)],[c_8229,c_3674]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8449,plain,
% 3.68/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 3.68/0.98      | sK5 = k1_xboole_0
% 3.68/0.98      | sK4 = k1_xboole_0
% 3.68/0.98      | sK3 = k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = X0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_8410,c_24]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8451,plain,
% 3.68/0.98      ( sK5 = k1_xboole_0
% 3.68/0.98      | sK4 = k1_xboole_0
% 3.68/0.98      | sK3 = k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = X0
% 3.68/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_8449,c_1417]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8452,plain,
% 3.68/0.98      ( sK5 = k1_xboole_0
% 3.68/0.98      | sK4 = k1_xboole_0
% 3.68/0.98      | sK3 = k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = X0 ),
% 3.68/0.98      inference(equality_resolution_simp,[status(thm)],[c_8451]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8691,plain,
% 3.68/0.98      ( k1_xboole_0 = X0 ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_2135,c_28,c_27,c_26,c_35,c_36,c_849,c_883,c_909,c_8452]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8736,plain,
% 3.68/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_8691,c_26]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8756,plain,
% 3.68/0.98      ( $false ),
% 3.68/0.98      inference(equality_resolution_simp,[status(thm)],[c_8736]) ).
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  ------                               Statistics
% 3.68/0.98  
% 3.68/0.98  ------ General
% 3.68/0.98  
% 3.68/0.98  abstr_ref_over_cycles:                  0
% 3.68/0.98  abstr_ref_under_cycles:                 0
% 3.68/0.98  gc_basic_clause_elim:                   0
% 3.68/0.98  forced_gc_time:                         0
% 3.68/0.98  parsing_time:                           0.007
% 3.68/0.98  unif_index_cands_time:                  0.
% 3.68/0.98  unif_index_add_time:                    0.
% 3.68/0.98  orderings_time:                         0.
% 3.68/0.98  out_proof_time:                         0.013
% 3.68/0.98  total_time:                             0.314
% 3.68/0.98  num_of_symbols:                         53
% 3.68/0.98  num_of_terms:                           14563
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing
% 3.68/0.98  
% 3.68/0.98  num_of_splits:                          0
% 3.68/0.98  num_of_split_atoms:                     0
% 3.68/0.98  num_of_reused_defs:                     0
% 3.68/0.98  num_eq_ax_congr_red:                    63
% 3.68/0.98  num_of_sem_filtered_clauses:            1
% 3.68/0.98  num_of_subtypes:                        0
% 3.68/0.98  monotx_restored_types:                  0
% 3.68/0.98  sat_num_of_epr_types:                   0
% 3.68/0.98  sat_num_of_non_cyclic_types:            0
% 3.68/0.98  sat_guarded_non_collapsed_types:        0
% 3.68/0.98  num_pure_diseq_elim:                    0
% 3.68/0.98  simp_replaced_by:                       0
% 3.68/0.98  res_preprocessed:                       138
% 3.68/0.98  prep_upred:                             0
% 3.68/0.98  prep_unflattend:                        1
% 3.68/0.98  smt_new_axioms:                         0
% 3.68/0.98  pred_elim_cands:                        4
% 3.68/0.98  pred_elim:                              1
% 3.68/0.98  pred_elim_cl:                           1
% 3.68/0.98  pred_elim_cycles:                       3
% 3.68/0.98  merged_defs:                            0
% 3.68/0.98  merged_defs_ncl:                        0
% 3.68/0.98  bin_hyper_res:                          0
% 3.68/0.98  prep_cycles:                            4
% 3.68/0.98  pred_elim_time:                         0.001
% 3.68/0.98  splitting_time:                         0.
% 3.68/0.98  sem_filter_time:                        0.
% 3.68/0.98  monotx_time:                            0.
% 3.68/0.98  subtype_inf_time:                       0.
% 3.68/0.98  
% 3.68/0.98  ------ Problem properties
% 3.68/0.98  
% 3.68/0.98  clauses:                                29
% 3.68/0.98  conjectures:                            6
% 3.68/0.98  epr:                                    8
% 3.68/0.98  horn:                                   23
% 3.68/0.98  ground:                                 5
% 3.68/0.98  unary:                                  10
% 3.68/0.98  binary:                                 7
% 3.68/0.98  lits:                                   70
% 3.68/0.98  lits_eq:                                35
% 3.68/0.98  fd_pure:                                0
% 3.68/0.98  fd_pseudo:                              0
% 3.68/0.98  fd_cond:                                8
% 3.68/0.98  fd_pseudo_cond:                         1
% 3.68/0.98  ac_symbols:                             0
% 3.68/0.98  
% 3.68/0.98  ------ Propositional Solver
% 3.68/0.98  
% 3.68/0.98  prop_solver_calls:                      28
% 3.68/0.98  prop_fast_solver_calls:                 1045
% 3.68/0.98  smt_solver_calls:                       0
% 3.68/0.98  smt_fast_solver_calls:                  0
% 3.68/0.98  prop_num_of_clauses:                    4278
% 3.68/0.98  prop_preprocess_simplified:             10223
% 3.68/0.98  prop_fo_subsumed:                       35
% 3.68/0.98  prop_solver_time:                       0.
% 3.68/0.98  smt_solver_time:                        0.
% 3.68/0.98  smt_fast_solver_time:                   0.
% 3.68/0.98  prop_fast_solver_time:                  0.
% 3.68/0.98  prop_unsat_core_time:                   0.
% 3.68/0.98  
% 3.68/0.98  ------ QBF
% 3.68/0.98  
% 3.68/0.98  qbf_q_res:                              0
% 3.68/0.98  qbf_num_tautologies:                    0
% 3.68/0.98  qbf_prep_cycles:                        0
% 3.68/0.98  
% 3.68/0.98  ------ BMC1
% 3.68/0.98  
% 3.68/0.98  bmc1_current_bound:                     -1
% 3.68/0.98  bmc1_last_solved_bound:                 -1
% 3.68/0.98  bmc1_unsat_core_size:                   -1
% 3.68/0.98  bmc1_unsat_core_parents_size:           -1
% 3.68/0.98  bmc1_merge_next_fun:                    0
% 3.68/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation
% 3.68/0.98  
% 3.68/0.98  inst_num_of_clauses:                    1237
% 3.68/0.98  inst_num_in_passive:                    130
% 3.68/0.98  inst_num_in_active:                     528
% 3.68/0.98  inst_num_in_unprocessed:                579
% 3.68/0.98  inst_num_of_loops:                      530
% 3.68/0.98  inst_num_of_learning_restarts:          0
% 3.68/0.98  inst_num_moves_active_passive:          2
% 3.68/0.98  inst_lit_activity:                      0
% 3.68/0.98  inst_lit_activity_moves:                0
% 3.68/0.98  inst_num_tautologies:                   0
% 3.68/0.98  inst_num_prop_implied:                  0
% 3.68/0.98  inst_num_existing_simplified:           0
% 3.68/0.98  inst_num_eq_res_simplified:             0
% 3.68/0.98  inst_num_child_elim:                    0
% 3.68/0.98  inst_num_of_dismatching_blockings:      154
% 3.68/0.98  inst_num_of_non_proper_insts:           1077
% 3.68/0.98  inst_num_of_duplicates:                 0
% 3.68/0.98  inst_inst_num_from_inst_to_res:         0
% 3.68/0.98  inst_dismatching_checking_time:         0.
% 3.68/0.98  
% 3.68/0.98  ------ Resolution
% 3.68/0.98  
% 3.68/0.98  res_num_of_clauses:                     0
% 3.68/0.98  res_num_in_passive:                     0
% 3.68/0.98  res_num_in_active:                      0
% 3.68/0.98  res_num_of_loops:                       142
% 3.68/0.98  res_forward_subset_subsumed:            51
% 3.68/0.98  res_backward_subset_subsumed:           0
% 3.68/0.98  res_forward_subsumed:                   0
% 3.68/0.98  res_backward_subsumed:                  0
% 3.68/0.98  res_forward_subsumption_resolution:     0
% 3.68/0.98  res_backward_subsumption_resolution:    0
% 3.68/0.98  res_clause_to_clause_subsumption:       881
% 3.68/0.98  res_orphan_elimination:                 0
% 3.68/0.98  res_tautology_del:                      12
% 3.68/0.98  res_num_eq_res_simplified:              0
% 3.68/0.98  res_num_sel_changes:                    0
% 3.68/0.98  res_moves_from_active_to_pass:          0
% 3.68/0.98  
% 3.68/0.98  ------ Superposition
% 3.68/0.98  
% 3.68/0.98  sup_time_total:                         0.
% 3.68/0.98  sup_time_generating:                    0.
% 3.68/0.98  sup_time_sim_full:                      0.
% 3.68/0.98  sup_time_sim_immed:                     0.
% 3.68/0.98  
% 3.68/0.98  sup_num_of_clauses:                     131
% 3.68/0.98  sup_num_in_active:                      6
% 3.68/0.98  sup_num_in_passive:                     125
% 3.68/0.98  sup_num_of_loops:                       105
% 3.68/0.98  sup_fw_superposition:                   224
% 3.68/0.98  sup_bw_superposition:                   1502
% 3.68/0.98  sup_immediate_simplified:               597
% 3.68/0.98  sup_given_eliminated:                   0
% 3.68/0.98  comparisons_done:                       0
% 3.68/0.98  comparisons_avoided:                    86
% 3.68/0.98  
% 3.68/0.98  ------ Simplifications
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  sim_fw_subset_subsumed:                 351
% 3.68/0.98  sim_bw_subset_subsumed:                 52
% 3.68/0.98  sim_fw_subsumed:                        172
% 3.68/0.98  sim_bw_subsumed:                        38
% 3.68/0.98  sim_fw_subsumption_res:                 0
% 3.68/0.98  sim_bw_subsumption_res:                 0
% 3.68/0.98  sim_tautology_del:                      16
% 3.68/0.98  sim_eq_tautology_del:                   65
% 3.68/0.98  sim_eq_res_simp:                        26
% 3.68/0.98  sim_fw_demodulated:                     51
% 3.68/0.98  sim_bw_demodulated:                     75
% 3.68/0.98  sim_light_normalised:                   16
% 3.68/0.98  sim_joinable_taut:                      0
% 3.68/0.98  sim_joinable_simp:                      0
% 3.68/0.98  sim_ac_normalised:                      0
% 3.68/0.98  sim_smt_subsumption:                    0
% 3.68/0.98  
%------------------------------------------------------------------------------
