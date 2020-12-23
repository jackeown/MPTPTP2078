%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:53 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 486 expanded)
%              Number of clauses        :   71 ( 155 expanded)
%              Number of leaves         :   16 ( 105 expanded)
%              Depth                    :   23
%              Number of atoms          :  407 (2123 expanded)
%              Number of equality atoms :  282 (1346 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f65])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f77,f89])).

fof(f120,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f106])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f76,f89])).

fof(f19,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f44,plain,
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
   => ( k5_mcart_1(sK2,sK3,sK4,sK6) != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK5 = X5
                  | k3_mcart_1(X5,X6,X7) != sK6
                  | ~ m1_subset_1(X7,sK4) )
              | ~ m1_subset_1(X6,sK3) )
          | ~ m1_subset_1(X5,sK2) )
      & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK6) != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK5 = X5
                | k3_mcart_1(X5,X6,X7) != sK6
                | ~ m1_subset_1(X7,sK4) )
            | ~ m1_subset_1(X6,sK3) )
        | ~ m1_subset_1(X5,sK2) )
    & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f33,f44])).

fof(f83,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f45])).

fof(f109,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f81,f65])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f40])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X5
      | k3_mcart_1(X5,X6,X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f108,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X5
      | k4_tarski(k4_tarski(X5,X6),X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(definition_unfolding,[],[f82,f64])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f73,f65])).

fof(f86,plain,(
    k5_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f79,f89])).

fof(f118,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f104])).

cnf(c_27,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_28,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1804,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) != k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3) = k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X4 ),
    inference(superposition,[status(thm)],[c_27,c_28])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_39,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_40,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_629,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1446,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_1447,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_1448,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_1449,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_1450,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_1451,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1450])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1184,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1194,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3504,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1184,c_1194])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_358,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_359,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_1183,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_3576,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3504,c_1183])).

cnf(c_20,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1189,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1206,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2557,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1189,c_1206])).

cnf(c_3653,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3576,c_2557])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1192,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3575,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3504,c_1192])).

cnf(c_3661,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3575,c_1183])).

cnf(c_4321,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3661,c_2557])).

cnf(c_33,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ m1_subset_1(X1,sK3)
    | ~ m1_subset_1(X2,sK2)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK6
    | sK5 = X2 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1185,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK6
    | sK5 = X0
    | m1_subset_1(X2,sK4) != iProver_top
    | m1_subset_1(X1,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5583,plain,
    ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k1_mcart_1(k1_mcart_1(sK6)) = sK5
    | m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4321,c_1185])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1186,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2298,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1184,c_1186])).

cnf(c_2914,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2298,c_32,c_31,c_30,c_39,c_40,c_1447,c_1449,c_1451])).

cnf(c_29,negated_conjecture,
    ( k5_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2917,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) != sK5 ),
    inference(demodulation,[status(thm)],[c_2914,c_29])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1193,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3659,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3575,c_1193])).

cnf(c_4277,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3659,c_2557])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1195,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5517,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4277,c_1195])).

cnf(c_3660,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3575,c_1192])).

cnf(c_4286,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3660,c_2557])).

cnf(c_5532,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4286,c_1195])).

cnf(c_5588,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),X0) != sK6
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5583,c_2917,c_5517,c_5532])).

cnf(c_5589,plain,
    ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_5588])).

cnf(c_5597,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK6),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3653,c_5589])).

cnf(c_3574,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK4) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3504,c_1193])).

cnf(c_3648,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3574,c_2557])).

cnf(c_3729,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3648,c_1195])).

cnf(c_5746,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5597,c_3729])).

cnf(c_5821,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_5746,c_28])).

cnf(c_25,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1617,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_25,c_25])).

cnf(c_5828,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5821,c_1617])).

cnf(c_5829,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5828])).

cnf(c_6475,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1804,c_32,c_31,c_30,c_39,c_40,c_1447,c_1449,c_1451,c_5829])).

cnf(c_6506,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6475,c_32])).

cnf(c_6527,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6506])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.82/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.01  
% 2.82/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.82/1.01  
% 2.82/1.01  ------  iProver source info
% 2.82/1.01  
% 2.82/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.82/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.82/1.01  git: non_committed_changes: false
% 2.82/1.01  git: last_make_outside_of_git: false
% 2.82/1.01  
% 2.82/1.01  ------ 
% 2.82/1.01  
% 2.82/1.01  ------ Input Options
% 2.82/1.01  
% 2.82/1.01  --out_options                           all
% 2.82/1.01  --tptp_safe_out                         true
% 2.82/1.01  --problem_path                          ""
% 2.82/1.01  --include_path                          ""
% 2.82/1.01  --clausifier                            res/vclausify_rel
% 2.82/1.01  --clausifier_options                    --mode clausify
% 2.82/1.01  --stdin                                 false
% 2.82/1.01  --stats_out                             all
% 2.82/1.01  
% 2.82/1.01  ------ General Options
% 2.82/1.01  
% 2.82/1.01  --fof                                   false
% 2.82/1.01  --time_out_real                         305.
% 2.82/1.01  --time_out_virtual                      -1.
% 2.82/1.01  --symbol_type_check                     false
% 2.82/1.01  --clausify_out                          false
% 2.82/1.01  --sig_cnt_out                           false
% 2.82/1.01  --trig_cnt_out                          false
% 2.82/1.01  --trig_cnt_out_tolerance                1.
% 2.82/1.01  --trig_cnt_out_sk_spl                   false
% 2.82/1.01  --abstr_cl_out                          false
% 2.82/1.01  
% 2.82/1.01  ------ Global Options
% 2.82/1.01  
% 2.82/1.01  --schedule                              default
% 2.82/1.01  --add_important_lit                     false
% 2.82/1.01  --prop_solver_per_cl                    1000
% 2.82/1.01  --min_unsat_core                        false
% 2.82/1.01  --soft_assumptions                      false
% 2.82/1.01  --soft_lemma_size                       3
% 2.82/1.01  --prop_impl_unit_size                   0
% 2.82/1.01  --prop_impl_unit                        []
% 2.82/1.01  --share_sel_clauses                     true
% 2.82/1.01  --reset_solvers                         false
% 2.82/1.01  --bc_imp_inh                            [conj_cone]
% 2.82/1.01  --conj_cone_tolerance                   3.
% 2.82/1.01  --extra_neg_conj                        none
% 2.82/1.01  --large_theory_mode                     true
% 2.82/1.01  --prolific_symb_bound                   200
% 2.82/1.01  --lt_threshold                          2000
% 2.82/1.01  --clause_weak_htbl                      true
% 2.82/1.01  --gc_record_bc_elim                     false
% 2.82/1.01  
% 2.82/1.01  ------ Preprocessing Options
% 2.82/1.01  
% 2.82/1.01  --preprocessing_flag                    true
% 2.82/1.01  --time_out_prep_mult                    0.1
% 2.82/1.01  --splitting_mode                        input
% 2.82/1.01  --splitting_grd                         true
% 2.82/1.01  --splitting_cvd                         false
% 2.82/1.01  --splitting_cvd_svl                     false
% 2.82/1.01  --splitting_nvd                         32
% 2.82/1.01  --sub_typing                            true
% 2.82/1.01  --prep_gs_sim                           true
% 2.82/1.01  --prep_unflatten                        true
% 2.82/1.01  --prep_res_sim                          true
% 2.82/1.01  --prep_upred                            true
% 2.82/1.01  --prep_sem_filter                       exhaustive
% 2.82/1.01  --prep_sem_filter_out                   false
% 2.82/1.01  --pred_elim                             true
% 2.82/1.01  --res_sim_input                         true
% 2.82/1.01  --eq_ax_congr_red                       true
% 2.82/1.01  --pure_diseq_elim                       true
% 2.82/1.01  --brand_transform                       false
% 2.82/1.01  --non_eq_to_eq                          false
% 2.82/1.01  --prep_def_merge                        true
% 2.82/1.01  --prep_def_merge_prop_impl              false
% 2.82/1.01  --prep_def_merge_mbd                    true
% 2.82/1.01  --prep_def_merge_tr_red                 false
% 2.82/1.01  --prep_def_merge_tr_cl                  false
% 2.82/1.01  --smt_preprocessing                     true
% 2.82/1.01  --smt_ac_axioms                         fast
% 2.82/1.01  --preprocessed_out                      false
% 2.82/1.01  --preprocessed_stats                    false
% 2.82/1.01  
% 2.82/1.01  ------ Abstraction refinement Options
% 2.82/1.01  
% 2.82/1.01  --abstr_ref                             []
% 2.82/1.01  --abstr_ref_prep                        false
% 2.82/1.01  --abstr_ref_until_sat                   false
% 2.82/1.01  --abstr_ref_sig_restrict                funpre
% 2.82/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/1.01  --abstr_ref_under                       []
% 2.82/1.01  
% 2.82/1.01  ------ SAT Options
% 2.82/1.01  
% 2.82/1.01  --sat_mode                              false
% 2.82/1.01  --sat_fm_restart_options                ""
% 2.82/1.01  --sat_gr_def                            false
% 2.82/1.01  --sat_epr_types                         true
% 2.82/1.01  --sat_non_cyclic_types                  false
% 2.82/1.01  --sat_finite_models                     false
% 2.82/1.01  --sat_fm_lemmas                         false
% 2.82/1.01  --sat_fm_prep                           false
% 2.82/1.01  --sat_fm_uc_incr                        true
% 2.82/1.01  --sat_out_model                         small
% 2.82/1.01  --sat_out_clauses                       false
% 2.82/1.01  
% 2.82/1.01  ------ QBF Options
% 2.82/1.01  
% 2.82/1.01  --qbf_mode                              false
% 2.82/1.01  --qbf_elim_univ                         false
% 2.82/1.01  --qbf_dom_inst                          none
% 2.82/1.01  --qbf_dom_pre_inst                      false
% 2.82/1.01  --qbf_sk_in                             false
% 2.82/1.01  --qbf_pred_elim                         true
% 2.82/1.01  --qbf_split                             512
% 2.82/1.01  
% 2.82/1.01  ------ BMC1 Options
% 2.82/1.01  
% 2.82/1.01  --bmc1_incremental                      false
% 2.82/1.01  --bmc1_axioms                           reachable_all
% 2.82/1.01  --bmc1_min_bound                        0
% 2.82/1.01  --bmc1_max_bound                        -1
% 2.82/1.01  --bmc1_max_bound_default                -1
% 2.82/1.01  --bmc1_symbol_reachability              true
% 2.82/1.01  --bmc1_property_lemmas                  false
% 2.82/1.01  --bmc1_k_induction                      false
% 2.82/1.01  --bmc1_non_equiv_states                 false
% 2.82/1.01  --bmc1_deadlock                         false
% 2.82/1.01  --bmc1_ucm                              false
% 2.82/1.01  --bmc1_add_unsat_core                   none
% 2.82/1.01  --bmc1_unsat_core_children              false
% 2.82/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/1.01  --bmc1_out_stat                         full
% 2.82/1.01  --bmc1_ground_init                      false
% 2.82/1.01  --bmc1_pre_inst_next_state              false
% 2.82/1.01  --bmc1_pre_inst_state                   false
% 2.82/1.01  --bmc1_pre_inst_reach_state             false
% 2.82/1.01  --bmc1_out_unsat_core                   false
% 2.82/1.01  --bmc1_aig_witness_out                  false
% 2.82/1.01  --bmc1_verbose                          false
% 2.82/1.01  --bmc1_dump_clauses_tptp                false
% 2.82/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.82/1.01  --bmc1_dump_file                        -
% 2.82/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.82/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.82/1.01  --bmc1_ucm_extend_mode                  1
% 2.82/1.01  --bmc1_ucm_init_mode                    2
% 2.82/1.01  --bmc1_ucm_cone_mode                    none
% 2.82/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.82/1.01  --bmc1_ucm_relax_model                  4
% 2.82/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.82/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/1.01  --bmc1_ucm_layered_model                none
% 2.82/1.01  --bmc1_ucm_max_lemma_size               10
% 2.82/1.01  
% 2.82/1.01  ------ AIG Options
% 2.82/1.01  
% 2.82/1.01  --aig_mode                              false
% 2.82/1.01  
% 2.82/1.01  ------ Instantiation Options
% 2.82/1.01  
% 2.82/1.01  --instantiation_flag                    true
% 2.82/1.01  --inst_sos_flag                         false
% 2.82/1.01  --inst_sos_phase                        true
% 2.82/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/1.01  --inst_lit_sel_side                     num_symb
% 2.82/1.01  --inst_solver_per_active                1400
% 2.82/1.01  --inst_solver_calls_frac                1.
% 2.82/1.01  --inst_passive_queue_type               priority_queues
% 2.82/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/1.01  --inst_passive_queues_freq              [25;2]
% 2.82/1.01  --inst_dismatching                      true
% 2.82/1.01  --inst_eager_unprocessed_to_passive     true
% 2.82/1.01  --inst_prop_sim_given                   true
% 2.82/1.01  --inst_prop_sim_new                     false
% 2.82/1.01  --inst_subs_new                         false
% 2.82/1.01  --inst_eq_res_simp                      false
% 2.82/1.01  --inst_subs_given                       false
% 2.82/1.01  --inst_orphan_elimination               true
% 2.82/1.01  --inst_learning_loop_flag               true
% 2.82/1.01  --inst_learning_start                   3000
% 2.82/1.01  --inst_learning_factor                  2
% 2.82/1.01  --inst_start_prop_sim_after_learn       3
% 2.82/1.01  --inst_sel_renew                        solver
% 2.82/1.01  --inst_lit_activity_flag                true
% 2.82/1.01  --inst_restr_to_given                   false
% 2.82/1.01  --inst_activity_threshold               500
% 2.82/1.01  --inst_out_proof                        true
% 2.82/1.01  
% 2.82/1.01  ------ Resolution Options
% 2.82/1.01  
% 2.82/1.01  --resolution_flag                       true
% 2.82/1.01  --res_lit_sel                           adaptive
% 2.82/1.01  --res_lit_sel_side                      none
% 2.82/1.01  --res_ordering                          kbo
% 2.82/1.01  --res_to_prop_solver                    active
% 2.82/1.01  --res_prop_simpl_new                    false
% 2.82/1.01  --res_prop_simpl_given                  true
% 2.82/1.01  --res_passive_queue_type                priority_queues
% 2.82/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/1.01  --res_passive_queues_freq               [15;5]
% 2.82/1.01  --res_forward_subs                      full
% 2.82/1.01  --res_backward_subs                     full
% 2.82/1.01  --res_forward_subs_resolution           true
% 2.82/1.01  --res_backward_subs_resolution          true
% 2.82/1.01  --res_orphan_elimination                true
% 2.82/1.01  --res_time_limit                        2.
% 2.82/1.01  --res_out_proof                         true
% 2.82/1.01  
% 2.82/1.01  ------ Superposition Options
% 2.82/1.01  
% 2.82/1.01  --superposition_flag                    true
% 2.82/1.01  --sup_passive_queue_type                priority_queues
% 2.82/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.82/1.01  --demod_completeness_check              fast
% 2.82/1.01  --demod_use_ground                      true
% 2.82/1.01  --sup_to_prop_solver                    passive
% 2.82/1.01  --sup_prop_simpl_new                    true
% 2.82/1.01  --sup_prop_simpl_given                  true
% 2.82/1.01  --sup_fun_splitting                     false
% 2.82/1.01  --sup_smt_interval                      50000
% 2.82/1.01  
% 2.82/1.01  ------ Superposition Simplification Setup
% 2.82/1.01  
% 2.82/1.01  --sup_indices_passive                   []
% 2.82/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.01  --sup_full_bw                           [BwDemod]
% 2.82/1.01  --sup_immed_triv                        [TrivRules]
% 2.82/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.01  --sup_immed_bw_main                     []
% 2.82/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.01  
% 2.82/1.01  ------ Combination Options
% 2.82/1.01  
% 2.82/1.01  --comb_res_mult                         3
% 2.82/1.01  --comb_sup_mult                         2
% 2.82/1.01  --comb_inst_mult                        10
% 2.82/1.01  
% 2.82/1.01  ------ Debug Options
% 2.82/1.01  
% 2.82/1.01  --dbg_backtrace                         false
% 2.82/1.01  --dbg_dump_prop_clauses                 false
% 2.82/1.01  --dbg_dump_prop_clauses_file            -
% 2.82/1.01  --dbg_out_stat                          false
% 2.82/1.01  ------ Parsing...
% 2.82/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.82/1.01  
% 2.82/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.82/1.01  
% 2.82/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.82/1.01  
% 2.82/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.82/1.01  ------ Proving...
% 2.82/1.01  ------ Problem Properties 
% 2.82/1.01  
% 2.82/1.01  
% 2.82/1.01  clauses                                 34
% 2.82/1.01  conjectures                             6
% 2.82/1.01  EPR                                     6
% 2.82/1.01  Horn                                    25
% 2.82/1.01  unary                                   13
% 2.82/1.01  binary                                  8
% 2.82/1.01  lits                                    81
% 2.82/1.01  lits eq                                 49
% 2.82/1.01  fd_pure                                 0
% 2.82/1.01  fd_pseudo                               0
% 2.82/1.01  fd_cond                                 8
% 2.82/1.01  fd_pseudo_cond                          4
% 2.82/1.01  AC symbols                              0
% 2.82/1.01  
% 2.82/1.01  ------ Schedule dynamic 5 is on 
% 2.82/1.01  
% 2.82/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.82/1.01  
% 2.82/1.01  
% 2.82/1.01  ------ 
% 2.82/1.01  Current options:
% 2.82/1.01  ------ 
% 2.82/1.01  
% 2.82/1.01  ------ Input Options
% 2.82/1.01  
% 2.82/1.01  --out_options                           all
% 2.82/1.01  --tptp_safe_out                         true
% 2.82/1.01  --problem_path                          ""
% 2.82/1.01  --include_path                          ""
% 2.82/1.01  --clausifier                            res/vclausify_rel
% 2.82/1.01  --clausifier_options                    --mode clausify
% 2.82/1.01  --stdin                                 false
% 2.82/1.01  --stats_out                             all
% 2.82/1.01  
% 2.82/1.01  ------ General Options
% 2.82/1.01  
% 2.82/1.01  --fof                                   false
% 2.82/1.01  --time_out_real                         305.
% 2.82/1.01  --time_out_virtual                      -1.
% 2.82/1.01  --symbol_type_check                     false
% 2.82/1.01  --clausify_out                          false
% 2.82/1.01  --sig_cnt_out                           false
% 2.82/1.01  --trig_cnt_out                          false
% 2.82/1.01  --trig_cnt_out_tolerance                1.
% 2.82/1.01  --trig_cnt_out_sk_spl                   false
% 2.82/1.01  --abstr_cl_out                          false
% 2.82/1.01  
% 2.82/1.01  ------ Global Options
% 2.82/1.01  
% 2.82/1.01  --schedule                              default
% 2.82/1.01  --add_important_lit                     false
% 2.82/1.01  --prop_solver_per_cl                    1000
% 2.82/1.01  --min_unsat_core                        false
% 2.82/1.01  --soft_assumptions                      false
% 2.82/1.01  --soft_lemma_size                       3
% 2.82/1.01  --prop_impl_unit_size                   0
% 2.82/1.01  --prop_impl_unit                        []
% 2.82/1.01  --share_sel_clauses                     true
% 2.82/1.01  --reset_solvers                         false
% 2.82/1.01  --bc_imp_inh                            [conj_cone]
% 2.82/1.01  --conj_cone_tolerance                   3.
% 2.82/1.01  --extra_neg_conj                        none
% 2.82/1.01  --large_theory_mode                     true
% 2.82/1.01  --prolific_symb_bound                   200
% 2.82/1.01  --lt_threshold                          2000
% 2.82/1.01  --clause_weak_htbl                      true
% 2.82/1.01  --gc_record_bc_elim                     false
% 2.82/1.01  
% 2.82/1.01  ------ Preprocessing Options
% 2.82/1.01  
% 2.82/1.01  --preprocessing_flag                    true
% 2.82/1.01  --time_out_prep_mult                    0.1
% 2.82/1.01  --splitting_mode                        input
% 2.82/1.01  --splitting_grd                         true
% 2.82/1.01  --splitting_cvd                         false
% 2.82/1.01  --splitting_cvd_svl                     false
% 2.82/1.01  --splitting_nvd                         32
% 2.82/1.01  --sub_typing                            true
% 2.82/1.01  --prep_gs_sim                           true
% 2.82/1.01  --prep_unflatten                        true
% 2.82/1.01  --prep_res_sim                          true
% 2.82/1.01  --prep_upred                            true
% 2.82/1.01  --prep_sem_filter                       exhaustive
% 2.82/1.01  --prep_sem_filter_out                   false
% 2.82/1.01  --pred_elim                             true
% 2.82/1.01  --res_sim_input                         true
% 2.82/1.01  --eq_ax_congr_red                       true
% 2.82/1.01  --pure_diseq_elim                       true
% 2.82/1.01  --brand_transform                       false
% 2.82/1.01  --non_eq_to_eq                          false
% 2.82/1.01  --prep_def_merge                        true
% 2.82/1.01  --prep_def_merge_prop_impl              false
% 2.82/1.01  --prep_def_merge_mbd                    true
% 2.82/1.01  --prep_def_merge_tr_red                 false
% 2.82/1.01  --prep_def_merge_tr_cl                  false
% 2.82/1.01  --smt_preprocessing                     true
% 2.82/1.01  --smt_ac_axioms                         fast
% 2.82/1.01  --preprocessed_out                      false
% 2.82/1.01  --preprocessed_stats                    false
% 2.82/1.01  
% 2.82/1.01  ------ Abstraction refinement Options
% 2.82/1.01  
% 2.82/1.01  --abstr_ref                             []
% 2.82/1.01  --abstr_ref_prep                        false
% 2.82/1.01  --abstr_ref_until_sat                   false
% 2.82/1.01  --abstr_ref_sig_restrict                funpre
% 2.82/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/1.01  --abstr_ref_under                       []
% 2.82/1.01  
% 2.82/1.01  ------ SAT Options
% 2.82/1.01  
% 2.82/1.01  --sat_mode                              false
% 2.82/1.01  --sat_fm_restart_options                ""
% 2.82/1.01  --sat_gr_def                            false
% 2.82/1.01  --sat_epr_types                         true
% 2.82/1.01  --sat_non_cyclic_types                  false
% 2.82/1.01  --sat_finite_models                     false
% 2.82/1.01  --sat_fm_lemmas                         false
% 2.82/1.01  --sat_fm_prep                           false
% 2.82/1.01  --sat_fm_uc_incr                        true
% 2.82/1.01  --sat_out_model                         small
% 2.82/1.01  --sat_out_clauses                       false
% 2.82/1.01  
% 2.82/1.01  ------ QBF Options
% 2.82/1.01  
% 2.82/1.01  --qbf_mode                              false
% 2.82/1.01  --qbf_elim_univ                         false
% 2.82/1.01  --qbf_dom_inst                          none
% 2.82/1.01  --qbf_dom_pre_inst                      false
% 2.82/1.01  --qbf_sk_in                             false
% 2.82/1.01  --qbf_pred_elim                         true
% 2.82/1.01  --qbf_split                             512
% 2.82/1.01  
% 2.82/1.01  ------ BMC1 Options
% 2.82/1.01  
% 2.82/1.01  --bmc1_incremental                      false
% 2.82/1.01  --bmc1_axioms                           reachable_all
% 2.82/1.01  --bmc1_min_bound                        0
% 2.82/1.01  --bmc1_max_bound                        -1
% 2.82/1.01  --bmc1_max_bound_default                -1
% 2.82/1.01  --bmc1_symbol_reachability              true
% 2.82/1.01  --bmc1_property_lemmas                  false
% 2.82/1.01  --bmc1_k_induction                      false
% 2.82/1.01  --bmc1_non_equiv_states                 false
% 2.82/1.01  --bmc1_deadlock                         false
% 2.82/1.01  --bmc1_ucm                              false
% 2.82/1.01  --bmc1_add_unsat_core                   none
% 2.82/1.01  --bmc1_unsat_core_children              false
% 2.82/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/1.01  --bmc1_out_stat                         full
% 2.82/1.01  --bmc1_ground_init                      false
% 2.82/1.01  --bmc1_pre_inst_next_state              false
% 2.82/1.01  --bmc1_pre_inst_state                   false
% 2.82/1.01  --bmc1_pre_inst_reach_state             false
% 2.82/1.01  --bmc1_out_unsat_core                   false
% 2.82/1.01  --bmc1_aig_witness_out                  false
% 2.82/1.01  --bmc1_verbose                          false
% 2.82/1.01  --bmc1_dump_clauses_tptp                false
% 2.82/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.82/1.01  --bmc1_dump_file                        -
% 2.82/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.82/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.82/1.01  --bmc1_ucm_extend_mode                  1
% 2.82/1.01  --bmc1_ucm_init_mode                    2
% 2.82/1.01  --bmc1_ucm_cone_mode                    none
% 2.82/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.82/1.01  --bmc1_ucm_relax_model                  4
% 2.82/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.82/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/1.01  --bmc1_ucm_layered_model                none
% 2.82/1.01  --bmc1_ucm_max_lemma_size               10
% 2.82/1.01  
% 2.82/1.01  ------ AIG Options
% 2.82/1.01  
% 2.82/1.01  --aig_mode                              false
% 2.82/1.01  
% 2.82/1.01  ------ Instantiation Options
% 2.82/1.01  
% 2.82/1.01  --instantiation_flag                    true
% 2.82/1.01  --inst_sos_flag                         false
% 2.82/1.01  --inst_sos_phase                        true
% 2.82/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/1.01  --inst_lit_sel_side                     none
% 2.82/1.01  --inst_solver_per_active                1400
% 2.82/1.01  --inst_solver_calls_frac                1.
% 2.82/1.01  --inst_passive_queue_type               priority_queues
% 2.82/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/1.01  --inst_passive_queues_freq              [25;2]
% 2.82/1.01  --inst_dismatching                      true
% 2.82/1.01  --inst_eager_unprocessed_to_passive     true
% 2.82/1.01  --inst_prop_sim_given                   true
% 2.82/1.01  --inst_prop_sim_new                     false
% 2.82/1.01  --inst_subs_new                         false
% 2.82/1.01  --inst_eq_res_simp                      false
% 2.82/1.01  --inst_subs_given                       false
% 2.82/1.01  --inst_orphan_elimination               true
% 2.82/1.01  --inst_learning_loop_flag               true
% 2.82/1.01  --inst_learning_start                   3000
% 2.82/1.01  --inst_learning_factor                  2
% 2.82/1.01  --inst_start_prop_sim_after_learn       3
% 2.82/1.01  --inst_sel_renew                        solver
% 2.82/1.01  --inst_lit_activity_flag                true
% 2.82/1.01  --inst_restr_to_given                   false
% 2.82/1.01  --inst_activity_threshold               500
% 2.82/1.01  --inst_out_proof                        true
% 2.82/1.01  
% 2.82/1.01  ------ Resolution Options
% 2.82/1.01  
% 2.82/1.01  --resolution_flag                       false
% 2.82/1.01  --res_lit_sel                           adaptive
% 2.82/1.01  --res_lit_sel_side                      none
% 2.82/1.01  --res_ordering                          kbo
% 2.82/1.01  --res_to_prop_solver                    active
% 2.82/1.01  --res_prop_simpl_new                    false
% 2.82/1.01  --res_prop_simpl_given                  true
% 2.82/1.01  --res_passive_queue_type                priority_queues
% 2.82/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/1.01  --res_passive_queues_freq               [15;5]
% 2.82/1.01  --res_forward_subs                      full
% 2.82/1.01  --res_backward_subs                     full
% 2.82/1.01  --res_forward_subs_resolution           true
% 2.82/1.01  --res_backward_subs_resolution          true
% 2.82/1.01  --res_orphan_elimination                true
% 2.82/1.01  --res_time_limit                        2.
% 2.82/1.01  --res_out_proof                         true
% 2.82/1.01  
% 2.82/1.01  ------ Superposition Options
% 2.82/1.01  
% 2.82/1.01  --superposition_flag                    true
% 2.82/1.01  --sup_passive_queue_type                priority_queues
% 2.82/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.82/1.01  --demod_completeness_check              fast
% 2.82/1.01  --demod_use_ground                      true
% 2.82/1.01  --sup_to_prop_solver                    passive
% 2.82/1.01  --sup_prop_simpl_new                    true
% 2.82/1.01  --sup_prop_simpl_given                  true
% 2.82/1.01  --sup_fun_splitting                     false
% 2.82/1.01  --sup_smt_interval                      50000
% 2.82/1.01  
% 2.82/1.01  ------ Superposition Simplification Setup
% 2.82/1.01  
% 2.82/1.01  --sup_indices_passive                   []
% 2.82/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.01  --sup_full_bw                           [BwDemod]
% 2.82/1.01  --sup_immed_triv                        [TrivRules]
% 2.82/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.01  --sup_immed_bw_main                     []
% 2.82/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/1.01  
% 2.82/1.01  ------ Combination Options
% 2.82/1.01  
% 2.82/1.01  --comb_res_mult                         3
% 2.82/1.01  --comb_sup_mult                         2
% 2.82/1.01  --comb_inst_mult                        10
% 2.82/1.01  
% 2.82/1.01  ------ Debug Options
% 2.82/1.01  
% 2.82/1.01  --dbg_backtrace                         false
% 2.82/1.01  --dbg_dump_prop_clauses                 false
% 2.82/1.01  --dbg_dump_prop_clauses_file            -
% 2.82/1.01  --dbg_out_stat                          false
% 2.82/1.01  
% 2.82/1.01  
% 2.82/1.01  
% 2.82/1.01  
% 2.82/1.01  ------ Proving...
% 2.82/1.01  
% 2.82/1.01  
% 2.82/1.01  % SZS status Theorem for theBenchmark.p
% 2.82/1.01  
% 2.82/1.01   Resolution empty clause
% 2.82/1.01  
% 2.82/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.82/1.01  
% 2.82/1.01  fof(f18,axiom,(
% 2.82/1.01    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f42,plain,(
% 2.82/1.01    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.82/1.01    inference(nnf_transformation,[],[f18])).
% 2.82/1.01  
% 2.82/1.01  fof(f43,plain,(
% 2.82/1.01    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.82/1.01    inference(flattening,[],[f42])).
% 2.82/1.01  
% 2.82/1.01  fof(f77,plain,(
% 2.82/1.01    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.82/1.01    inference(cnf_transformation,[],[f43])).
% 2.82/1.01  
% 2.82/1.01  fof(f13,axiom,(
% 2.82/1.01    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f66,plain,(
% 2.82/1.01    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.82/1.01    inference(cnf_transformation,[],[f13])).
% 2.82/1.01  
% 2.82/1.01  fof(f12,axiom,(
% 2.82/1.01    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f65,plain,(
% 2.82/1.01    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 2.82/1.01    inference(cnf_transformation,[],[f12])).
% 2.82/1.01  
% 2.82/1.01  fof(f89,plain,(
% 2.82/1.01    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.82/1.01    inference(definition_unfolding,[],[f66,f65])).
% 2.82/1.01  
% 2.82/1.01  fof(f106,plain,(
% 2.82/1.01    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.82/1.01    inference(definition_unfolding,[],[f77,f89])).
% 2.82/1.01  
% 2.82/1.01  fof(f120,plain,(
% 2.82/1.01    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 2.82/1.01    inference(equality_resolution,[],[f106])).
% 2.82/1.01  
% 2.82/1.01  fof(f76,plain,(
% 2.82/1.01    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.82/1.01    inference(cnf_transformation,[],[f43])).
% 2.82/1.01  
% 2.82/1.01  fof(f107,plain,(
% 2.82/1.01    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.82/1.01    inference(definition_unfolding,[],[f76,f89])).
% 2.82/1.01  
% 2.82/1.01  fof(f19,conjecture,(
% 2.82/1.01    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f20,negated_conjecture,(
% 2.82/1.01    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.82/1.01    inference(negated_conjecture,[],[f19])).
% 2.82/1.01  
% 2.82/1.01  fof(f32,plain,(
% 2.82/1.01    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.82/1.01    inference(ennf_transformation,[],[f20])).
% 2.82/1.01  
% 2.82/1.01  fof(f33,plain,(
% 2.82/1.01    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.82/1.01    inference(flattening,[],[f32])).
% 2.82/1.01  
% 2.82/1.01  fof(f44,plain,(
% 2.82/1.01    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k5_mcart_1(sK2,sK3,sK4,sK6) != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X5 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)))),
% 2.82/1.01    introduced(choice_axiom,[])).
% 2.82/1.01  
% 2.82/1.01  fof(f45,plain,(
% 2.82/1.01    k5_mcart_1(sK2,sK3,sK4,sK6) != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X5 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 2.82/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f33,f44])).
% 2.82/1.01  
% 2.82/1.01  fof(f83,plain,(
% 2.82/1.01    k1_xboole_0 != sK2),
% 2.82/1.01    inference(cnf_transformation,[],[f45])).
% 2.82/1.01  
% 2.82/1.01  fof(f84,plain,(
% 2.82/1.01    k1_xboole_0 != sK3),
% 2.82/1.01    inference(cnf_transformation,[],[f45])).
% 2.82/1.01  
% 2.82/1.01  fof(f85,plain,(
% 2.82/1.01    k1_xboole_0 != sK4),
% 2.82/1.01    inference(cnf_transformation,[],[f45])).
% 2.82/1.01  
% 2.82/1.01  fof(f81,plain,(
% 2.82/1.01    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 2.82/1.01    inference(cnf_transformation,[],[f45])).
% 2.82/1.01  
% 2.82/1.01  fof(f109,plain,(
% 2.82/1.01    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 2.82/1.01    inference(definition_unfolding,[],[f81,f65])).
% 2.82/1.01  
% 2.82/1.01  fof(f9,axiom,(
% 2.82/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f25,plain,(
% 2.82/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.82/1.01    inference(ennf_transformation,[],[f9])).
% 2.82/1.01  
% 2.82/1.01  fof(f26,plain,(
% 2.82/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.82/1.01    inference(flattening,[],[f25])).
% 2.82/1.01  
% 2.82/1.01  fof(f62,plain,(
% 2.82/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.82/1.01    inference(cnf_transformation,[],[f26])).
% 2.82/1.01  
% 2.82/1.01  fof(f10,axiom,(
% 2.82/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f63,plain,(
% 2.82/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.82/1.01    inference(cnf_transformation,[],[f10])).
% 2.82/1.01  
% 2.82/1.01  fof(f15,axiom,(
% 2.82/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f28,plain,(
% 2.82/1.01    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 2.82/1.01    inference(ennf_transformation,[],[f15])).
% 2.82/1.01  
% 2.82/1.01  fof(f29,plain,(
% 2.82/1.01    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 2.82/1.01    inference(flattening,[],[f28])).
% 2.82/1.01  
% 2.82/1.01  fof(f69,plain,(
% 2.82/1.01    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 2.82/1.01    inference(cnf_transformation,[],[f29])).
% 2.82/1.01  
% 2.82/1.01  fof(f16,axiom,(
% 2.82/1.01    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f30,plain,(
% 2.82/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.82/1.01    inference(ennf_transformation,[],[f16])).
% 2.82/1.01  
% 2.82/1.01  fof(f40,plain,(
% 2.82/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 2.82/1.01    introduced(choice_axiom,[])).
% 2.82/1.01  
% 2.82/1.01  fof(f41,plain,(
% 2.82/1.01    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 2.82/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f40])).
% 2.82/1.01  
% 2.82/1.01  fof(f70,plain,(
% 2.82/1.01    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.82/1.01    inference(cnf_transformation,[],[f41])).
% 2.82/1.01  
% 2.82/1.01  fof(f1,axiom,(
% 2.82/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f21,plain,(
% 2.82/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.82/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 2.82/1.01  
% 2.82/1.01  fof(f22,plain,(
% 2.82/1.01    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.82/1.01    inference(ennf_transformation,[],[f21])).
% 2.82/1.01  
% 2.82/1.01  fof(f46,plain,(
% 2.82/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.82/1.01    inference(cnf_transformation,[],[f22])).
% 2.82/1.01  
% 2.82/1.01  fof(f14,axiom,(
% 2.82/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f27,plain,(
% 2.82/1.01    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.82/1.01    inference(ennf_transformation,[],[f14])).
% 2.82/1.01  
% 2.82/1.01  fof(f67,plain,(
% 2.82/1.01    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.82/1.01    inference(cnf_transformation,[],[f27])).
% 2.82/1.01  
% 2.82/1.01  fof(f82,plain,(
% 2.82/1.01    ( ! [X6,X7,X5] : (sK5 = X5 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 2.82/1.01    inference(cnf_transformation,[],[f45])).
% 2.82/1.01  
% 2.82/1.01  fof(f11,axiom,(
% 2.82/1.01    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f64,plain,(
% 2.82/1.01    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.82/1.01    inference(cnf_transformation,[],[f11])).
% 2.82/1.01  
% 2.82/1.01  fof(f108,plain,(
% 2.82/1.01    ( ! [X6,X7,X5] : (sK5 = X5 | k4_tarski(k4_tarski(X5,X6),X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 2.82/1.01    inference(definition_unfolding,[],[f82,f64])).
% 2.82/1.01  
% 2.82/1.01  fof(f17,axiom,(
% 2.82/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f31,plain,(
% 2.82/1.01    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.82/1.01    inference(ennf_transformation,[],[f17])).
% 2.82/1.01  
% 2.82/1.01  fof(f73,plain,(
% 2.82/1.01    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.82/1.01    inference(cnf_transformation,[],[f31])).
% 2.82/1.01  
% 2.82/1.01  fof(f102,plain,(
% 2.82/1.01    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.82/1.01    inference(definition_unfolding,[],[f73,f65])).
% 2.82/1.01  
% 2.82/1.01  fof(f86,plain,(
% 2.82/1.01    k5_mcart_1(sK2,sK3,sK4,sK6) != sK5),
% 2.82/1.01    inference(cnf_transformation,[],[f45])).
% 2.82/1.01  
% 2.82/1.01  fof(f68,plain,(
% 2.82/1.01    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.82/1.01    inference(cnf_transformation,[],[f27])).
% 2.82/1.01  
% 2.82/1.01  fof(f8,axiom,(
% 2.82/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.82/1.01  
% 2.82/1.01  fof(f24,plain,(
% 2.82/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.82/1.01    inference(ennf_transformation,[],[f8])).
% 2.82/1.01  
% 2.82/1.01  fof(f61,plain,(
% 2.82/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.82/1.01    inference(cnf_transformation,[],[f24])).
% 2.82/1.01  
% 2.82/1.01  fof(f79,plain,(
% 2.82/1.01    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.82/1.01    inference(cnf_transformation,[],[f43])).
% 2.82/1.01  
% 2.82/1.01  fof(f104,plain,(
% 2.82/1.01    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.82/1.01    inference(definition_unfolding,[],[f79,f89])).
% 2.82/1.01  
% 2.82/1.01  fof(f118,plain,(
% 2.82/1.01    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 2.82/1.01    inference(equality_resolution,[],[f104])).
% 2.82/1.01  
% 2.82/1.01  cnf(c_27,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 2.82/1.01      inference(cnf_transformation,[],[f120]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_28,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 2.82/1.01      | k1_xboole_0 = X0
% 2.82/1.01      | k1_xboole_0 = X1
% 2.82/1.01      | k1_xboole_0 = X2
% 2.82/1.01      | k1_xboole_0 = X3 ),
% 2.82/1.01      inference(cnf_transformation,[],[f107]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1804,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) != k1_xboole_0
% 2.82/1.01      | k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3) = k1_xboole_0
% 2.82/1.01      | k1_xboole_0 = X1
% 2.82/1.01      | k1_xboole_0 = X0
% 2.82/1.01      | k1_xboole_0 = X4 ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_27,c_28]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_32,negated_conjecture,
% 2.82/1.01      ( k1_xboole_0 != sK2 ),
% 2.82/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_31,negated_conjecture,
% 2.82/1.01      ( k1_xboole_0 != sK3 ),
% 2.82/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_30,negated_conjecture,
% 2.82/1.01      ( k1_xboole_0 != sK4 ),
% 2.82/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_39,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 2.82/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 2.82/1.01      inference(instantiation,[status(thm)],[c_28]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_40,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 2.82/1.01      inference(instantiation,[status(thm)],[c_27]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_629,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1446,plain,
% 2.82/1.01      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.82/1.01      inference(instantiation,[status(thm)],[c_629]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1447,plain,
% 2.82/1.01      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 2.82/1.01      inference(instantiation,[status(thm)],[c_1446]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1448,plain,
% 2.82/1.01      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.82/1.01      inference(instantiation,[status(thm)],[c_629]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1449,plain,
% 2.82/1.01      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.82/1.01      inference(instantiation,[status(thm)],[c_1448]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1450,plain,
% 2.82/1.01      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 2.82/1.01      inference(instantiation,[status(thm)],[c_629]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1451,plain,
% 2.82/1.01      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 2.82/1.01      inference(instantiation,[status(thm)],[c_1450]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_34,negated_conjecture,
% 2.82/1.01      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 2.82/1.01      inference(cnf_transformation,[],[f109]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1184,plain,
% 2.82/1.01      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 2.82/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_13,plain,
% 2.82/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.82/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1194,plain,
% 2.82/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.82/1.01      | r2_hidden(X0,X1) = iProver_top
% 2.82/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.82/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_3504,plain,
% 2.82/1.01      ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top
% 2.82/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_1184,c_1194]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_14,plain,
% 2.82/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.82/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_17,plain,
% 2.82/1.01      ( ~ r2_hidden(X0,X1)
% 2.82/1.01      | ~ v1_relat_1(X1)
% 2.82/1.01      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 2.82/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_358,plain,
% 2.82/1.01      ( ~ r2_hidden(X0,X1)
% 2.82/1.01      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 2.82/1.01      | k2_zfmisc_1(X2,X3) != X1 ),
% 2.82/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_359,plain,
% 2.82/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.82/1.01      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 2.82/1.01      inference(unflattening,[status(thm)],[c_358]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1183,plain,
% 2.82/1.01      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 2.82/1.01      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 2.82/1.01      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_3576,plain,
% 2.82/1.01      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 2.82/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3504,c_1183]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_20,plain,
% 2.82/1.01      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.82/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1189,plain,
% 2.82/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.82/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_0,plain,
% 2.82/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.82/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1206,plain,
% 2.82/1.01      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 2.82/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_2557,plain,
% 2.82/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_1189,c_1206]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_3653,plain,
% 2.82/1.01      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 2.82/1.01      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3576,c_2557]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_16,plain,
% 2.82/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.82/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1192,plain,
% 2.82/1.01      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.82/1.01      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 2.82/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_3575,plain,
% 2.82/1.01      ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top
% 2.82/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3504,c_1192]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_3661,plain,
% 2.82/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 2.82/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3575,c_1183]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_4321,plain,
% 2.82/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 2.82/1.01      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3661,c_2557]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_33,negated_conjecture,
% 2.82/1.01      ( ~ m1_subset_1(X0,sK4)
% 2.82/1.01      | ~ m1_subset_1(X1,sK3)
% 2.82/1.01      | ~ m1_subset_1(X2,sK2)
% 2.82/1.01      | k4_tarski(k4_tarski(X2,X1),X0) != sK6
% 2.82/1.01      | sK5 = X2 ),
% 2.82/1.01      inference(cnf_transformation,[],[f108]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1185,plain,
% 2.82/1.01      ( k4_tarski(k4_tarski(X0,X1),X2) != sK6
% 2.82/1.01      | sK5 = X0
% 2.82/1.01      | m1_subset_1(X2,sK4) != iProver_top
% 2.82/1.01      | m1_subset_1(X1,sK3) != iProver_top
% 2.82/1.01      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.82/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_5583,plain,
% 2.82/1.01      ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
% 2.82/1.01      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 2.82/1.01      | k1_mcart_1(k1_mcart_1(sK6)) = sK5
% 2.82/1.01      | m1_subset_1(X0,sK4) != iProver_top
% 2.82/1.01      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) != iProver_top
% 2.82/1.01      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) != iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_4321,c_1185]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_23,plain,
% 2.82/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.82/1.01      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.82/1.01      | k1_xboole_0 = X1
% 2.82/1.01      | k1_xboole_0 = X2
% 2.82/1.01      | k1_xboole_0 = X3 ),
% 2.82/1.01      inference(cnf_transformation,[],[f102]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1186,plain,
% 2.82/1.01      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.82/1.01      | k1_xboole_0 = X0
% 2.82/1.01      | k1_xboole_0 = X1
% 2.82/1.01      | k1_xboole_0 = X2
% 2.82/1.01      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.82/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_2298,plain,
% 2.82/1.01      ( k5_mcart_1(sK2,sK3,sK4,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 2.82/1.01      | sK4 = k1_xboole_0
% 2.82/1.01      | sK3 = k1_xboole_0
% 2.82/1.01      | sK2 = k1_xboole_0 ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_1184,c_1186]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_2914,plain,
% 2.82/1.01      ( k5_mcart_1(sK2,sK3,sK4,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
% 2.82/1.01      inference(global_propositional_subsumption,
% 2.82/1.01                [status(thm)],
% 2.82/1.01                [c_2298,c_32,c_31,c_30,c_39,c_40,c_1447,c_1449,c_1451]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_29,negated_conjecture,
% 2.82/1.01      ( k5_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
% 2.82/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_2917,plain,
% 2.82/1.01      ( k1_mcart_1(k1_mcart_1(sK6)) != sK5 ),
% 2.82/1.01      inference(demodulation,[status(thm)],[c_2914,c_29]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_15,plain,
% 2.82/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.82/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1193,plain,
% 2.82/1.01      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.82/1.01      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 2.82/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_3659,plain,
% 2.82/1.01      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top
% 2.82/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3575,c_1193]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_4277,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 2.82/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3659,c_2557]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_12,plain,
% 2.82/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.82/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1195,plain,
% 2.82/1.01      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 2.82/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_5517,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 2.82/1.01      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_4277,c_1195]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_3660,plain,
% 2.82/1.01      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top
% 2.82/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3575,c_1192]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_4286,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 2.82/1.01      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3660,c_2557]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_5532,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 2.82/1.01      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_4286,c_1195]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_5588,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 2.82/1.01      | k4_tarski(k1_mcart_1(sK6),X0) != sK6
% 2.82/1.01      | m1_subset_1(X0,sK4) != iProver_top ),
% 2.82/1.01      inference(global_propositional_subsumption,
% 2.82/1.01                [status(thm)],
% 2.82/1.01                [c_5583,c_2917,c_5517,c_5532]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_5589,plain,
% 2.82/1.01      ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
% 2.82/1.01      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 2.82/1.01      | m1_subset_1(X0,sK4) != iProver_top ),
% 2.82/1.01      inference(renaming,[status(thm)],[c_5588]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_5597,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 2.82/1.01      | m1_subset_1(k2_mcart_1(sK6),sK4) != iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3653,c_5589]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_3574,plain,
% 2.82/1.01      ( r2_hidden(k2_mcart_1(sK6),sK4) = iProver_top
% 2.82/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3504,c_1193]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_3648,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 2.82/1.01      | r2_hidden(k2_mcart_1(sK6),sK4) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3574,c_2557]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_3729,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 2.82/1.01      | m1_subset_1(k2_mcart_1(sK6),sK4) = iProver_top ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_3648,c_1195]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_5746,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
% 2.82/1.01      inference(global_propositional_subsumption,[status(thm)],[c_5597,c_3729]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_5821,plain,
% 2.82/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 2.82/1.01      | sK4 = k1_xboole_0
% 2.82/1.01      | sK3 = k1_xboole_0
% 2.82/1.01      | sK2 = k1_xboole_0
% 2.82/1.01      | k1_xboole_0 = X0 ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_5746,c_28]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_25,plain,
% 2.82/1.01      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
% 2.82/1.01      inference(cnf_transformation,[],[f118]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_1617,plain,
% 2.82/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.82/1.01      inference(superposition,[status(thm)],[c_25,c_25]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_5828,plain,
% 2.82/1.01      ( sK4 = k1_xboole_0
% 2.82/1.01      | sK3 = k1_xboole_0
% 2.82/1.01      | sK2 = k1_xboole_0
% 2.82/1.01      | k1_xboole_0 = X0
% 2.82/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.82/1.01      inference(light_normalisation,[status(thm)],[c_5821,c_1617]) ).
% 2.82/1.01  
% 2.82/1.01  cnf(c_5829,plain,
% 2.82/1.01      ( sK4 = k1_xboole_0
% 2.82/1.01      | sK3 = k1_xboole_0
% 2.82/1.02      | sK2 = k1_xboole_0
% 2.82/1.02      | k1_xboole_0 = X0 ),
% 2.82/1.02      inference(equality_resolution_simp,[status(thm)],[c_5828]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_6475,plain,
% 2.82/1.02      ( k1_xboole_0 = X0 ),
% 2.82/1.02      inference(global_propositional_subsumption,
% 2.82/1.02                [status(thm)],
% 2.82/1.02                [c_1804,c_32,c_31,c_30,c_39,c_40,c_1447,c_1449,c_1451,c_5829]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_6506,plain,
% 2.82/1.02      ( k1_xboole_0 != k1_xboole_0 ),
% 2.82/1.02      inference(demodulation,[status(thm)],[c_6475,c_32]) ).
% 2.82/1.02  
% 2.82/1.02  cnf(c_6527,plain,
% 2.82/1.02      ( $false ),
% 2.82/1.02      inference(equality_resolution_simp,[status(thm)],[c_6506]) ).
% 2.82/1.02  
% 2.82/1.02  
% 2.82/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.82/1.02  
% 2.82/1.02  ------                               Statistics
% 2.82/1.02  
% 2.82/1.02  ------ General
% 2.82/1.02  
% 2.82/1.02  abstr_ref_over_cycles:                  0
% 2.82/1.02  abstr_ref_under_cycles:                 0
% 2.82/1.02  gc_basic_clause_elim:                   0
% 2.82/1.02  forced_gc_time:                         0
% 2.82/1.02  parsing_time:                           0.011
% 2.82/1.02  unif_index_cands_time:                  0.
% 2.82/1.02  unif_index_add_time:                    0.
% 2.82/1.02  orderings_time:                         0.
% 2.82/1.02  out_proof_time:                         0.01
% 2.82/1.02  total_time:                             0.198
% 2.82/1.02  num_of_symbols:                         53
% 2.82/1.02  num_of_terms:                           7091
% 2.82/1.02  
% 2.82/1.02  ------ Preprocessing
% 2.82/1.02  
% 2.82/1.02  num_of_splits:                          0
% 2.82/1.02  num_of_split_atoms:                     0
% 2.82/1.02  num_of_reused_defs:                     0
% 2.82/1.02  num_eq_ax_congr_red:                    66
% 2.82/1.02  num_of_sem_filtered_clauses:            1
% 2.82/1.02  num_of_subtypes:                        0
% 2.82/1.02  monotx_restored_types:                  0
% 2.82/1.02  sat_num_of_epr_types:                   0
% 2.82/1.02  sat_num_of_non_cyclic_types:            0
% 2.82/1.02  sat_guarded_non_collapsed_types:        0
% 2.82/1.02  num_pure_diseq_elim:                    0
% 2.82/1.02  simp_replaced_by:                       0
% 2.82/1.02  res_preprocessed:                       158
% 2.82/1.02  prep_upred:                             0
% 2.82/1.02  prep_unflattend:                        1
% 2.82/1.02  smt_new_axioms:                         0
% 2.82/1.02  pred_elim_cands:                        3
% 2.82/1.02  pred_elim:                              1
% 2.82/1.02  pred_elim_cl:                           1
% 2.82/1.02  pred_elim_cycles:                       3
% 2.82/1.02  merged_defs:                            8
% 2.82/1.02  merged_defs_ncl:                        0
% 2.82/1.02  bin_hyper_res:                          8
% 2.82/1.02  prep_cycles:                            4
% 2.82/1.02  pred_elim_time:                         0.001
% 2.82/1.02  splitting_time:                         0.
% 2.82/1.02  sem_filter_time:                        0.
% 2.82/1.02  monotx_time:                            0.
% 2.82/1.02  subtype_inf_time:                       0.
% 2.82/1.02  
% 2.82/1.02  ------ Problem properties
% 2.82/1.02  
% 2.82/1.02  clauses:                                34
% 2.82/1.02  conjectures:                            6
% 2.82/1.02  epr:                                    6
% 2.82/1.02  horn:                                   25
% 2.82/1.02  ground:                                 5
% 2.82/1.02  unary:                                  13
% 2.82/1.02  binary:                                 8
% 2.82/1.02  lits:                                   81
% 2.82/1.02  lits_eq:                                49
% 2.82/1.02  fd_pure:                                0
% 2.82/1.02  fd_pseudo:                              0
% 2.82/1.02  fd_cond:                                8
% 2.82/1.02  fd_pseudo_cond:                         4
% 2.82/1.02  ac_symbols:                             0
% 2.82/1.02  
% 2.82/1.02  ------ Propositional Solver
% 2.82/1.02  
% 2.82/1.02  prop_solver_calls:                      27
% 2.82/1.02  prop_fast_solver_calls:                 986
% 2.82/1.02  smt_solver_calls:                       0
% 2.82/1.02  smt_fast_solver_calls:                  0
% 2.82/1.02  prop_num_of_clauses:                    2069
% 2.82/1.02  prop_preprocess_simplified:             7455
% 2.82/1.02  prop_fo_subsumed:                       22
% 2.82/1.02  prop_solver_time:                       0.
% 2.82/1.02  smt_solver_time:                        0.
% 2.82/1.02  smt_fast_solver_time:                   0.
% 2.82/1.02  prop_fast_solver_time:                  0.
% 2.82/1.02  prop_unsat_core_time:                   0.
% 2.82/1.02  
% 2.82/1.02  ------ QBF
% 2.82/1.02  
% 2.82/1.02  qbf_q_res:                              0
% 2.82/1.02  qbf_num_tautologies:                    0
% 2.82/1.02  qbf_prep_cycles:                        0
% 2.82/1.02  
% 2.82/1.02  ------ BMC1
% 2.82/1.02  
% 2.82/1.02  bmc1_current_bound:                     -1
% 2.82/1.02  bmc1_last_solved_bound:                 -1
% 2.82/1.02  bmc1_unsat_core_size:                   -1
% 2.82/1.02  bmc1_unsat_core_parents_size:           -1
% 2.82/1.02  bmc1_merge_next_fun:                    0
% 2.82/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.82/1.02  
% 2.82/1.02  ------ Instantiation
% 2.82/1.02  
% 2.82/1.02  inst_num_of_clauses:                    773
% 2.82/1.02  inst_num_in_passive:                    48
% 2.82/1.02  inst_num_in_active:                     343
% 2.82/1.02  inst_num_in_unprocessed:                382
% 2.82/1.02  inst_num_of_loops:                      360
% 2.82/1.02  inst_num_of_learning_restarts:          0
% 2.82/1.02  inst_num_moves_active_passive:          16
% 2.82/1.02  inst_lit_activity:                      0
% 2.82/1.02  inst_lit_activity_moves:                0
% 2.82/1.02  inst_num_tautologies:                   0
% 2.82/1.02  inst_num_prop_implied:                  0
% 2.82/1.02  inst_num_existing_simplified:           0
% 2.82/1.02  inst_num_eq_res_simplified:             0
% 2.82/1.02  inst_num_child_elim:                    0
% 2.82/1.02  inst_num_of_dismatching_blockings:      30
% 2.82/1.02  inst_num_of_non_proper_insts:           502
% 2.82/1.02  inst_num_of_duplicates:                 0
% 2.82/1.02  inst_inst_num_from_inst_to_res:         0
% 2.82/1.02  inst_dismatching_checking_time:         0.
% 2.82/1.02  
% 2.82/1.02  ------ Resolution
% 2.82/1.02  
% 2.82/1.02  res_num_of_clauses:                     0
% 2.82/1.02  res_num_in_passive:                     0
% 2.82/1.02  res_num_in_active:                      0
% 2.82/1.02  res_num_of_loops:                       162
% 2.82/1.02  res_forward_subset_subsumed:            18
% 2.82/1.02  res_backward_subset_subsumed:           0
% 2.82/1.02  res_forward_subsumed:                   0
% 2.82/1.02  res_backward_subsumed:                  0
% 2.82/1.02  res_forward_subsumption_resolution:     0
% 2.82/1.02  res_backward_subsumption_resolution:    0
% 2.82/1.02  res_clause_to_clause_subsumption:       400
% 2.82/1.02  res_orphan_elimination:                 0
% 2.82/1.02  res_tautology_del:                      18
% 2.82/1.02  res_num_eq_res_simplified:              0
% 2.82/1.02  res_num_sel_changes:                    0
% 2.82/1.02  res_moves_from_active_to_pass:          0
% 2.82/1.02  
% 2.82/1.02  ------ Superposition
% 2.82/1.02  
% 2.82/1.02  sup_time_total:                         0.
% 2.82/1.02  sup_time_generating:                    0.
% 2.82/1.02  sup_time_sim_full:                      0.
% 2.82/1.02  sup_time_sim_immed:                     0.
% 2.82/1.02  
% 2.82/1.02  sup_num_of_clauses:                     51
% 2.82/1.02  sup_num_in_active:                      8
% 2.82/1.02  sup_num_in_passive:                     43
% 2.82/1.02  sup_num_of_loops:                       70
% 2.82/1.02  sup_fw_superposition:                   137
% 2.82/1.02  sup_bw_superposition:                   1134
% 2.82/1.02  sup_immediate_simplified:               339
% 2.82/1.02  sup_given_eliminated:                   0
% 2.82/1.02  comparisons_done:                       0
% 2.82/1.02  comparisons_avoided:                    15
% 2.82/1.02  
% 2.82/1.02  ------ Simplifications
% 2.82/1.02  
% 2.82/1.02  
% 2.82/1.02  sim_fw_subset_subsumed:                 208
% 2.82/1.02  sim_bw_subset_subsumed:                 19
% 2.82/1.02  sim_fw_subsumed:                        134
% 2.82/1.02  sim_bw_subsumed:                        3
% 2.82/1.02  sim_fw_subsumption_res:                 1
% 2.82/1.02  sim_bw_subsumption_res:                 0
% 2.82/1.02  sim_tautology_del:                      19
% 2.82/1.02  sim_eq_tautology_del:                   50
% 2.82/1.02  sim_eq_res_simp:                        32
% 2.82/1.02  sim_fw_demodulated:                     14
% 2.82/1.02  sim_bw_demodulated:                     51
% 2.82/1.02  sim_light_normalised:                   8
% 2.82/1.02  sim_joinable_taut:                      0
% 2.82/1.02  sim_joinable_simp:                      0
% 2.82/1.02  sim_ac_normalised:                      0
% 2.82/1.02  sim_smt_subsumption:                    0
% 2.82/1.02  
%------------------------------------------------------------------------------
