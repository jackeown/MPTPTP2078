%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:04 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  194 (5484 expanded)
%              Number of clauses        :  119 (1608 expanded)
%              Number of leaves         :   18 (1225 expanded)
%              Depth                    :   31
%              Number of atoms          :  579 (21813 expanded)
%              Number of equality atoms :  458 (15019 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f34,plain,
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

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f27,f34])).

fof(f60,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f60,f41])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK0(X0),sK1(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK0(X0),sK1(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f28])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK0(X0),sK1(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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

fof(f31,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f30])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f41])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f80,plain,(
    ! [X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f71])).

fof(f62,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f82,plain,(
    ! [X2,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f73])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f81,plain,(
    ! [X2,X0,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f72])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f41])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f41])).

fof(f65,plain,(
    k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X7
      | k3_mcart_1(X5,X6,X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(definition_unfolding,[],[f61,f40])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_453,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_463,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2780,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_463])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK0(X0),sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_465,plain,
    ( k4_tarski(sK0(X0),sK1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2792,plain,
    ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2780,c_465])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_458,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_466,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2150,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_458,c_466])).

cnf(c_2826,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(sK0(sK7),sK1(sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_2792,c_2150])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_456,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3197,plain,
    ( k6_mcart_1(k2_zfmisc_1(sK3,sK4),sK5,X0,X1) = k2_mcart_1(k1_mcart_1(X1))
    | k2_zfmisc_1(sK3,sK4) = k1_xboole_0
    | k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | sK5 = k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2826,c_456])).

cnf(c_15,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_907,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15,c_15])).

cnf(c_3299,plain,
    ( k6_mcart_1(k2_zfmisc_1(sK3,sK4),sK5,X0,X1) = k2_mcart_1(k1_mcart_1(X1))
    | k2_zfmisc_1(sK3,sK4) = k1_xboole_0
    | k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | sK5 = k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3197,c_907])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_18,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_33,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_34,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_202,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_638,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_639,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_640,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_641,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_640])).

cnf(c_642,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_643,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_3207,plain,
    ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2826,c_2792])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_462,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2581,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK2(k2_zfmisc_1(X0,X1))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_458,c_462])).

cnf(c_10384,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2581,c_466])).

cnf(c_10439,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | k4_tarski(sK0(sK7),sK1(sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_3207,c_10384])).

cnf(c_3210,plain,
    ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | m1_subset_1(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2826,c_453])).

cnf(c_16,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_455,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_932,plain,
    ( k5_mcart_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1),X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | m1_subset_1(X4,k2_zfmisc_1(k1_xboole_0,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_455])).

cnf(c_3987,plain,
    ( k5_mcart_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1),X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_932,c_907])).

cnf(c_3994,plain,
    ( k5_mcart_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1),X2,X3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0
    | k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(superposition,[status(thm)],[c_3210,c_3987])).

cnf(c_11927,plain,
    ( k5_mcart_1(k2_zfmisc_1(k1_xboole_0,X0),X1,X2,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | k2_zfmisc_1(k2_zfmisc_1(X3,k1_xboole_0),X0) = k1_xboole_0
    | k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(superposition,[status(thm)],[c_10439,c_3994])).

cnf(c_11941,plain,
    ( k5_mcart_1(k1_xboole_0,X0,X1,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | k2_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0),X3) = k1_xboole_0
    | k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(light_normalisation,[status(thm)],[c_11927,c_907])).

cnf(c_3202,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_2826,c_18])).

cnf(c_3258,plain,
    ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3202,c_907])).

cnf(c_3259,plain,
    ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3258])).

cnf(c_16908,plain,
    ( k1_xboole_0 = X0
    | k4_tarski(sK0(sK7),sK1(sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11941,c_24,c_23,c_22,c_33,c_34,c_639,c_641,c_643,c_3259])).

cnf(c_16909,plain,
    ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_16908])).

cnf(c_19,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_17269,plain,
    ( k2_mcart_1(sK7) = sK1(sK7)
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_16909,c_19])).

cnf(c_6,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_492,plain,
    ( k4_tarski(X0,X1) != X1 ),
    inference(light_normalisation,[status(thm)],[c_6,c_19])).

cnf(c_18540,plain,
    ( k2_mcart_1(sK7) = sK1(sK7)
    | k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_17269,c_492])).

cnf(c_18713,plain,
    ( k2_mcart_1(sK7) = sK1(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18540,c_17269])).

cnf(c_2793,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK5) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2780,c_462])).

cnf(c_2821,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2793,c_2150])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_464,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2872,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2821,c_464])).

cnf(c_19103,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(sK1(sK7),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18713,c_2872])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_457,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2654,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_453,c_457])).

cnf(c_2813,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2654,c_24,c_23,c_22,c_33,c_34,c_639,c_641,c_643])).

cnf(c_21,negated_conjecture,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2816,plain,
    ( k2_mcart_1(sK7) != sK6 ),
    inference(demodulation,[status(thm)],[c_2813,c_21])).

cnf(c_19107,plain,
    ( sK1(sK7) != sK6 ),
    inference(demodulation,[status(thm)],[c_18713,c_2816])).

cnf(c_17228,plain,
    ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7
    | k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_16909,c_492])).

cnf(c_17480,plain,
    ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17228,c_16909])).

cnf(c_20,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_17268,plain,
    ( k1_mcart_1(sK7) = sK0(sK7)
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_16909,c_20])).

cnf(c_17934,plain,
    ( k1_mcart_1(sK7) = sK0(sK7)
    | k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_17268,c_492])).

cnf(c_18162,plain,
    ( k1_mcart_1(sK7) = sK0(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17934,c_17268])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_461,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2794,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2780,c_461])).

cnf(c_2834,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2794,c_461])).

cnf(c_3461,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2834,c_2150])).

cnf(c_4788,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3461,c_464])).

cnf(c_2832,plain,
    ( k4_tarski(sK0(k1_mcart_1(sK7)),sK1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2794,c_465])).

cnf(c_2155,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r2_hidden(k1_mcart_1(sK2(k2_zfmisc_1(X0,X1))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_458,c_461])).

cnf(c_8362,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2155,c_466])).

cnf(c_8421,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) = k1_xboole_0
    | k4_tarski(sK0(k1_mcart_1(sK7)),sK1(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
    inference(superposition,[status(thm)],[c_2832,c_8362])).

cnf(c_13634,plain,
    ( k4_tarski(sK0(k1_mcart_1(sK7)),sK1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_8421,c_18])).

cnf(c_14113,plain,
    ( k4_tarski(sK0(k1_mcart_1(sK7)),sK1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13634,c_24,c_23,c_22,c_33,c_34,c_639,c_641,c_643])).

cnf(c_14551,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = sK0(k1_mcart_1(sK7))
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_14113,c_20])).

cnf(c_15252,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = sK0(k1_mcart_1(sK7))
    | k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_14551,c_492])).

cnf(c_15413,plain,
    ( k1_mcart_1(k1_mcart_1(sK7)) = sK0(k1_mcart_1(sK7)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15252,c_14551])).

cnf(c_16876,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(sK0(k1_mcart_1(sK7)),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4788,c_15413])).

cnf(c_18759,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(sK0(sK0(sK7)),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18162,c_16876])).

cnf(c_2833,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2794,c_462])).

cnf(c_3448,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2833,c_2150])).

cnf(c_4763,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3448,c_464])).

cnf(c_14552,plain,
    ( k2_mcart_1(k1_mcart_1(sK7)) = sK1(k1_mcart_1(sK7))
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_14113,c_19])).

cnf(c_15782,plain,
    ( k2_mcart_1(k1_mcart_1(sK7)) = sK1(k1_mcart_1(sK7))
    | k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_14552,c_492])).

cnf(c_15957,plain,
    ( k2_mcart_1(k1_mcart_1(sK7)) = sK1(k1_mcart_1(sK7)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15782,c_14552])).

cnf(c_16796,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(sK1(k1_mcart_1(sK7)),sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4763,c_15957])).

cnf(c_18760,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(sK1(sK0(sK7)),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18162,c_16796])).

cnf(c_4441,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(sK0(k1_mcart_1(sK7)),sK1(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
    inference(superposition,[status(thm)],[c_2832,c_2150])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ m1_subset_1(X1,sK4)
    | ~ m1_subset_1(X2,sK3)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK7
    | sK6 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_454,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
    | sK6 = X2
    | m1_subset_1(X2,sK5) != iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4807,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK7),X0) != sK7
    | sK6 = X0
    | m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK1(k1_mcart_1(sK7)),sK4) != iProver_top
    | m1_subset_1(sK0(k1_mcart_1(sK7)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4441,c_454])).

cnf(c_18776,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(sK0(sK7),X0) != sK7
    | sK6 = X0
    | m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK1(sK0(sK7)),sK4) != iProver_top
    | m1_subset_1(sK0(sK0(sK7)),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18162,c_4807])).

cnf(c_18880,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(sK0(sK7),X0) != sK7
    | sK6 = X0
    | m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK0(sK0(sK7)),sK3) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_18760,c_18776])).

cnf(c_18895,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | k4_tarski(sK0(sK7),X0) != sK7
    | sK6 = X0
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_18759,c_18880])).

cnf(c_20051,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | sK1(sK7) = sK6
    | m1_subset_1(sK1(sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_17480,c_18895])).

cnf(c_20281,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19103,c_19107,c_20051])).

cnf(c_20381,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_20281,c_18])).

cnf(c_20410,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20381,c_907])).

cnf(c_20411,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_20410])).

cnf(c_20493,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3299,c_24,c_23,c_22,c_33,c_34,c_639,c_641,c_643,c_20411])).

cnf(c_20573,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20493,c_23])).

cnf(c_20615,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_20573])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:22:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.79/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.03  
% 3.79/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/1.03  
% 3.79/1.03  ------  iProver source info
% 3.79/1.03  
% 3.79/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.79/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/1.03  git: non_committed_changes: false
% 3.79/1.03  git: last_make_outside_of_git: false
% 3.79/1.03  
% 3.79/1.03  ------ 
% 3.79/1.03  
% 3.79/1.03  ------ Input Options
% 3.79/1.03  
% 3.79/1.03  --out_options                           all
% 3.79/1.03  --tptp_safe_out                         true
% 3.79/1.03  --problem_path                          ""
% 3.79/1.03  --include_path                          ""
% 3.79/1.03  --clausifier                            res/vclausify_rel
% 3.79/1.03  --clausifier_options                    --mode clausify
% 3.79/1.03  --stdin                                 false
% 3.79/1.03  --stats_out                             all
% 3.79/1.03  
% 3.79/1.03  ------ General Options
% 3.79/1.03  
% 3.79/1.03  --fof                                   false
% 3.79/1.03  --time_out_real                         305.
% 3.79/1.03  --time_out_virtual                      -1.
% 3.79/1.03  --symbol_type_check                     false
% 3.79/1.03  --clausify_out                          false
% 3.79/1.03  --sig_cnt_out                           false
% 3.79/1.03  --trig_cnt_out                          false
% 3.79/1.03  --trig_cnt_out_tolerance                1.
% 3.79/1.03  --trig_cnt_out_sk_spl                   false
% 3.79/1.03  --abstr_cl_out                          false
% 3.79/1.03  
% 3.79/1.03  ------ Global Options
% 3.79/1.03  
% 3.79/1.03  --schedule                              default
% 3.79/1.03  --add_important_lit                     false
% 3.79/1.03  --prop_solver_per_cl                    1000
% 3.79/1.03  --min_unsat_core                        false
% 3.79/1.03  --soft_assumptions                      false
% 3.79/1.03  --soft_lemma_size                       3
% 3.79/1.03  --prop_impl_unit_size                   0
% 3.79/1.03  --prop_impl_unit                        []
% 3.79/1.03  --share_sel_clauses                     true
% 3.79/1.03  --reset_solvers                         false
% 3.79/1.03  --bc_imp_inh                            [conj_cone]
% 3.79/1.03  --conj_cone_tolerance                   3.
% 3.79/1.03  --extra_neg_conj                        none
% 3.79/1.03  --large_theory_mode                     true
% 3.79/1.03  --prolific_symb_bound                   200
% 3.79/1.03  --lt_threshold                          2000
% 3.79/1.03  --clause_weak_htbl                      true
% 3.79/1.03  --gc_record_bc_elim                     false
% 3.79/1.03  
% 3.79/1.03  ------ Preprocessing Options
% 3.79/1.03  
% 3.79/1.03  --preprocessing_flag                    true
% 3.79/1.03  --time_out_prep_mult                    0.1
% 3.79/1.03  --splitting_mode                        input
% 3.79/1.03  --splitting_grd                         true
% 3.79/1.03  --splitting_cvd                         false
% 3.79/1.03  --splitting_cvd_svl                     false
% 3.79/1.03  --splitting_nvd                         32
% 3.79/1.03  --sub_typing                            true
% 3.79/1.03  --prep_gs_sim                           true
% 3.79/1.03  --prep_unflatten                        true
% 3.79/1.03  --prep_res_sim                          true
% 3.79/1.03  --prep_upred                            true
% 3.79/1.03  --prep_sem_filter                       exhaustive
% 3.79/1.03  --prep_sem_filter_out                   false
% 3.79/1.03  --pred_elim                             true
% 3.79/1.03  --res_sim_input                         true
% 3.79/1.03  --eq_ax_congr_red                       true
% 3.79/1.03  --pure_diseq_elim                       true
% 3.79/1.03  --brand_transform                       false
% 3.79/1.03  --non_eq_to_eq                          false
% 3.79/1.03  --prep_def_merge                        true
% 3.79/1.03  --prep_def_merge_prop_impl              false
% 3.79/1.03  --prep_def_merge_mbd                    true
% 3.79/1.03  --prep_def_merge_tr_red                 false
% 3.79/1.03  --prep_def_merge_tr_cl                  false
% 3.79/1.03  --smt_preprocessing                     true
% 3.79/1.03  --smt_ac_axioms                         fast
% 3.79/1.03  --preprocessed_out                      false
% 3.79/1.03  --preprocessed_stats                    false
% 3.79/1.03  
% 3.79/1.03  ------ Abstraction refinement Options
% 3.79/1.03  
% 3.79/1.03  --abstr_ref                             []
% 3.79/1.03  --abstr_ref_prep                        false
% 3.79/1.03  --abstr_ref_until_sat                   false
% 3.79/1.03  --abstr_ref_sig_restrict                funpre
% 3.79/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/1.03  --abstr_ref_under                       []
% 3.79/1.03  
% 3.79/1.03  ------ SAT Options
% 3.79/1.03  
% 3.79/1.03  --sat_mode                              false
% 3.79/1.03  --sat_fm_restart_options                ""
% 3.79/1.03  --sat_gr_def                            false
% 3.79/1.03  --sat_epr_types                         true
% 3.79/1.03  --sat_non_cyclic_types                  false
% 3.79/1.03  --sat_finite_models                     false
% 3.79/1.03  --sat_fm_lemmas                         false
% 3.79/1.03  --sat_fm_prep                           false
% 3.79/1.03  --sat_fm_uc_incr                        true
% 3.79/1.03  --sat_out_model                         small
% 3.79/1.03  --sat_out_clauses                       false
% 3.79/1.03  
% 3.79/1.03  ------ QBF Options
% 3.79/1.03  
% 3.79/1.03  --qbf_mode                              false
% 3.79/1.03  --qbf_elim_univ                         false
% 3.79/1.03  --qbf_dom_inst                          none
% 3.79/1.03  --qbf_dom_pre_inst                      false
% 3.79/1.03  --qbf_sk_in                             false
% 3.79/1.03  --qbf_pred_elim                         true
% 3.79/1.03  --qbf_split                             512
% 3.79/1.03  
% 3.79/1.03  ------ BMC1 Options
% 3.79/1.03  
% 3.79/1.03  --bmc1_incremental                      false
% 3.79/1.03  --bmc1_axioms                           reachable_all
% 3.79/1.03  --bmc1_min_bound                        0
% 3.79/1.03  --bmc1_max_bound                        -1
% 3.79/1.03  --bmc1_max_bound_default                -1
% 3.79/1.03  --bmc1_symbol_reachability              true
% 3.79/1.03  --bmc1_property_lemmas                  false
% 3.79/1.03  --bmc1_k_induction                      false
% 3.79/1.03  --bmc1_non_equiv_states                 false
% 3.79/1.03  --bmc1_deadlock                         false
% 3.79/1.03  --bmc1_ucm                              false
% 3.79/1.03  --bmc1_add_unsat_core                   none
% 3.79/1.03  --bmc1_unsat_core_children              false
% 3.79/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/1.03  --bmc1_out_stat                         full
% 3.79/1.03  --bmc1_ground_init                      false
% 3.79/1.03  --bmc1_pre_inst_next_state              false
% 3.79/1.03  --bmc1_pre_inst_state                   false
% 3.79/1.03  --bmc1_pre_inst_reach_state             false
% 3.79/1.03  --bmc1_out_unsat_core                   false
% 3.79/1.03  --bmc1_aig_witness_out                  false
% 3.79/1.03  --bmc1_verbose                          false
% 3.79/1.03  --bmc1_dump_clauses_tptp                false
% 3.79/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.79/1.03  --bmc1_dump_file                        -
% 3.79/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.79/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.79/1.03  --bmc1_ucm_extend_mode                  1
% 3.79/1.03  --bmc1_ucm_init_mode                    2
% 3.79/1.03  --bmc1_ucm_cone_mode                    none
% 3.79/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.79/1.03  --bmc1_ucm_relax_model                  4
% 3.79/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.79/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/1.03  --bmc1_ucm_layered_model                none
% 3.79/1.03  --bmc1_ucm_max_lemma_size               10
% 3.79/1.03  
% 3.79/1.03  ------ AIG Options
% 3.79/1.03  
% 3.79/1.03  --aig_mode                              false
% 3.79/1.03  
% 3.79/1.03  ------ Instantiation Options
% 3.79/1.03  
% 3.79/1.03  --instantiation_flag                    true
% 3.79/1.03  --inst_sos_flag                         false
% 3.79/1.03  --inst_sos_phase                        true
% 3.79/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/1.03  --inst_lit_sel_side                     num_symb
% 3.79/1.03  --inst_solver_per_active                1400
% 3.79/1.03  --inst_solver_calls_frac                1.
% 3.79/1.03  --inst_passive_queue_type               priority_queues
% 3.79/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/1.03  --inst_passive_queues_freq              [25;2]
% 3.79/1.03  --inst_dismatching                      true
% 3.79/1.03  --inst_eager_unprocessed_to_passive     true
% 3.79/1.03  --inst_prop_sim_given                   true
% 3.79/1.03  --inst_prop_sim_new                     false
% 3.79/1.03  --inst_subs_new                         false
% 3.79/1.03  --inst_eq_res_simp                      false
% 3.79/1.03  --inst_subs_given                       false
% 3.79/1.03  --inst_orphan_elimination               true
% 3.79/1.03  --inst_learning_loop_flag               true
% 3.79/1.03  --inst_learning_start                   3000
% 3.79/1.03  --inst_learning_factor                  2
% 3.79/1.03  --inst_start_prop_sim_after_learn       3
% 3.79/1.03  --inst_sel_renew                        solver
% 3.79/1.03  --inst_lit_activity_flag                true
% 3.79/1.03  --inst_restr_to_given                   false
% 3.79/1.03  --inst_activity_threshold               500
% 3.79/1.03  --inst_out_proof                        true
% 3.79/1.03  
% 3.79/1.03  ------ Resolution Options
% 3.79/1.03  
% 3.79/1.03  --resolution_flag                       true
% 3.79/1.03  --res_lit_sel                           adaptive
% 3.79/1.03  --res_lit_sel_side                      none
% 3.79/1.03  --res_ordering                          kbo
% 3.79/1.03  --res_to_prop_solver                    active
% 3.79/1.03  --res_prop_simpl_new                    false
% 3.79/1.03  --res_prop_simpl_given                  true
% 3.79/1.03  --res_passive_queue_type                priority_queues
% 3.79/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/1.03  --res_passive_queues_freq               [15;5]
% 3.79/1.03  --res_forward_subs                      full
% 3.79/1.03  --res_backward_subs                     full
% 3.79/1.03  --res_forward_subs_resolution           true
% 3.79/1.03  --res_backward_subs_resolution          true
% 3.79/1.03  --res_orphan_elimination                true
% 3.79/1.03  --res_time_limit                        2.
% 3.79/1.03  --res_out_proof                         true
% 3.79/1.03  
% 3.79/1.03  ------ Superposition Options
% 3.79/1.03  
% 3.79/1.03  --superposition_flag                    true
% 3.79/1.03  --sup_passive_queue_type                priority_queues
% 3.79/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.79/1.03  --demod_completeness_check              fast
% 3.79/1.03  --demod_use_ground                      true
% 3.79/1.03  --sup_to_prop_solver                    passive
% 3.79/1.03  --sup_prop_simpl_new                    true
% 3.79/1.03  --sup_prop_simpl_given                  true
% 3.79/1.03  --sup_fun_splitting                     false
% 3.79/1.03  --sup_smt_interval                      50000
% 3.79/1.03  
% 3.79/1.03  ------ Superposition Simplification Setup
% 3.79/1.03  
% 3.79/1.03  --sup_indices_passive                   []
% 3.79/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.03  --sup_full_bw                           [BwDemod]
% 3.79/1.03  --sup_immed_triv                        [TrivRules]
% 3.79/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.03  --sup_immed_bw_main                     []
% 3.79/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.03  
% 3.79/1.03  ------ Combination Options
% 3.79/1.03  
% 3.79/1.03  --comb_res_mult                         3
% 3.79/1.03  --comb_sup_mult                         2
% 3.79/1.03  --comb_inst_mult                        10
% 3.79/1.03  
% 3.79/1.03  ------ Debug Options
% 3.79/1.03  
% 3.79/1.03  --dbg_backtrace                         false
% 3.79/1.03  --dbg_dump_prop_clauses                 false
% 3.79/1.03  --dbg_dump_prop_clauses_file            -
% 3.79/1.03  --dbg_out_stat                          false
% 3.79/1.03  ------ Parsing...
% 3.79/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/1.03  
% 3.79/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.79/1.03  
% 3.79/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/1.03  
% 3.79/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/1.03  ------ Proving...
% 3.79/1.03  ------ Problem Properties 
% 3.79/1.03  
% 3.79/1.03  
% 3.79/1.03  clauses                                 27
% 3.79/1.03  conjectures                             6
% 3.79/1.03  EPR                                     6
% 3.79/1.03  Horn                                    21
% 3.79/1.03  unary                                   13
% 3.79/1.03  binary                                  6
% 3.79/1.03  lits                                    59
% 3.79/1.03  lits eq                                 37
% 3.79/1.03  fd_pure                                 0
% 3.79/1.03  fd_pseudo                               0
% 3.79/1.03  fd_cond                                 8
% 3.79/1.03  fd_pseudo_cond                          0
% 3.79/1.03  AC symbols                              0
% 3.79/1.03  
% 3.79/1.03  ------ Schedule dynamic 5 is on 
% 3.79/1.03  
% 3.79/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.79/1.03  
% 3.79/1.03  
% 3.79/1.03  ------ 
% 3.79/1.03  Current options:
% 3.79/1.03  ------ 
% 3.79/1.03  
% 3.79/1.03  ------ Input Options
% 3.79/1.03  
% 3.79/1.03  --out_options                           all
% 3.79/1.03  --tptp_safe_out                         true
% 3.79/1.03  --problem_path                          ""
% 3.79/1.03  --include_path                          ""
% 3.79/1.03  --clausifier                            res/vclausify_rel
% 3.79/1.03  --clausifier_options                    --mode clausify
% 3.79/1.03  --stdin                                 false
% 3.79/1.03  --stats_out                             all
% 3.79/1.03  
% 3.79/1.03  ------ General Options
% 3.79/1.03  
% 3.79/1.03  --fof                                   false
% 3.79/1.03  --time_out_real                         305.
% 3.79/1.03  --time_out_virtual                      -1.
% 3.79/1.03  --symbol_type_check                     false
% 3.79/1.03  --clausify_out                          false
% 3.79/1.03  --sig_cnt_out                           false
% 3.79/1.03  --trig_cnt_out                          false
% 3.79/1.03  --trig_cnt_out_tolerance                1.
% 3.79/1.03  --trig_cnt_out_sk_spl                   false
% 3.79/1.03  --abstr_cl_out                          false
% 3.79/1.03  
% 3.79/1.03  ------ Global Options
% 3.79/1.03  
% 3.79/1.03  --schedule                              default
% 3.79/1.03  --add_important_lit                     false
% 3.79/1.03  --prop_solver_per_cl                    1000
% 3.79/1.03  --min_unsat_core                        false
% 3.79/1.03  --soft_assumptions                      false
% 3.79/1.03  --soft_lemma_size                       3
% 3.79/1.03  --prop_impl_unit_size                   0
% 3.79/1.03  --prop_impl_unit                        []
% 3.79/1.03  --share_sel_clauses                     true
% 3.79/1.03  --reset_solvers                         false
% 3.79/1.03  --bc_imp_inh                            [conj_cone]
% 3.79/1.03  --conj_cone_tolerance                   3.
% 3.79/1.03  --extra_neg_conj                        none
% 3.79/1.03  --large_theory_mode                     true
% 3.79/1.03  --prolific_symb_bound                   200
% 3.79/1.03  --lt_threshold                          2000
% 3.79/1.03  --clause_weak_htbl                      true
% 3.79/1.03  --gc_record_bc_elim                     false
% 3.79/1.03  
% 3.79/1.03  ------ Preprocessing Options
% 3.79/1.03  
% 3.79/1.03  --preprocessing_flag                    true
% 3.79/1.03  --time_out_prep_mult                    0.1
% 3.79/1.03  --splitting_mode                        input
% 3.79/1.03  --splitting_grd                         true
% 3.79/1.03  --splitting_cvd                         false
% 3.79/1.03  --splitting_cvd_svl                     false
% 3.79/1.03  --splitting_nvd                         32
% 3.79/1.03  --sub_typing                            true
% 3.79/1.03  --prep_gs_sim                           true
% 3.79/1.03  --prep_unflatten                        true
% 3.79/1.03  --prep_res_sim                          true
% 3.79/1.03  --prep_upred                            true
% 3.79/1.03  --prep_sem_filter                       exhaustive
% 3.79/1.03  --prep_sem_filter_out                   false
% 3.79/1.03  --pred_elim                             true
% 3.79/1.03  --res_sim_input                         true
% 3.79/1.03  --eq_ax_congr_red                       true
% 3.79/1.03  --pure_diseq_elim                       true
% 3.79/1.03  --brand_transform                       false
% 3.79/1.03  --non_eq_to_eq                          false
% 3.79/1.03  --prep_def_merge                        true
% 3.79/1.03  --prep_def_merge_prop_impl              false
% 3.79/1.03  --prep_def_merge_mbd                    true
% 3.79/1.03  --prep_def_merge_tr_red                 false
% 3.79/1.03  --prep_def_merge_tr_cl                  false
% 3.79/1.03  --smt_preprocessing                     true
% 3.79/1.03  --smt_ac_axioms                         fast
% 3.79/1.03  --preprocessed_out                      false
% 3.79/1.03  --preprocessed_stats                    false
% 3.79/1.03  
% 3.79/1.03  ------ Abstraction refinement Options
% 3.79/1.03  
% 3.79/1.03  --abstr_ref                             []
% 3.79/1.03  --abstr_ref_prep                        false
% 3.79/1.03  --abstr_ref_until_sat                   false
% 3.79/1.03  --abstr_ref_sig_restrict                funpre
% 3.79/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/1.03  --abstr_ref_under                       []
% 3.79/1.03  
% 3.79/1.03  ------ SAT Options
% 3.79/1.03  
% 3.79/1.03  --sat_mode                              false
% 3.79/1.03  --sat_fm_restart_options                ""
% 3.79/1.03  --sat_gr_def                            false
% 3.79/1.03  --sat_epr_types                         true
% 3.79/1.03  --sat_non_cyclic_types                  false
% 3.79/1.03  --sat_finite_models                     false
% 3.79/1.03  --sat_fm_lemmas                         false
% 3.79/1.03  --sat_fm_prep                           false
% 3.79/1.03  --sat_fm_uc_incr                        true
% 3.79/1.03  --sat_out_model                         small
% 3.79/1.03  --sat_out_clauses                       false
% 3.79/1.03  
% 3.79/1.03  ------ QBF Options
% 3.79/1.03  
% 3.79/1.03  --qbf_mode                              false
% 3.79/1.03  --qbf_elim_univ                         false
% 3.79/1.03  --qbf_dom_inst                          none
% 3.79/1.03  --qbf_dom_pre_inst                      false
% 3.79/1.03  --qbf_sk_in                             false
% 3.79/1.03  --qbf_pred_elim                         true
% 3.79/1.03  --qbf_split                             512
% 3.79/1.03  
% 3.79/1.03  ------ BMC1 Options
% 3.79/1.03  
% 3.79/1.03  --bmc1_incremental                      false
% 3.79/1.03  --bmc1_axioms                           reachable_all
% 3.79/1.03  --bmc1_min_bound                        0
% 3.79/1.03  --bmc1_max_bound                        -1
% 3.79/1.03  --bmc1_max_bound_default                -1
% 3.79/1.03  --bmc1_symbol_reachability              true
% 3.79/1.03  --bmc1_property_lemmas                  false
% 3.79/1.03  --bmc1_k_induction                      false
% 3.79/1.03  --bmc1_non_equiv_states                 false
% 3.79/1.03  --bmc1_deadlock                         false
% 3.79/1.03  --bmc1_ucm                              false
% 3.79/1.03  --bmc1_add_unsat_core                   none
% 3.79/1.03  --bmc1_unsat_core_children              false
% 3.79/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/1.03  --bmc1_out_stat                         full
% 3.79/1.03  --bmc1_ground_init                      false
% 3.79/1.03  --bmc1_pre_inst_next_state              false
% 3.79/1.03  --bmc1_pre_inst_state                   false
% 3.79/1.03  --bmc1_pre_inst_reach_state             false
% 3.79/1.03  --bmc1_out_unsat_core                   false
% 3.79/1.03  --bmc1_aig_witness_out                  false
% 3.79/1.03  --bmc1_verbose                          false
% 3.79/1.03  --bmc1_dump_clauses_tptp                false
% 3.79/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.79/1.03  --bmc1_dump_file                        -
% 3.79/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.79/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.79/1.03  --bmc1_ucm_extend_mode                  1
% 3.79/1.03  --bmc1_ucm_init_mode                    2
% 3.79/1.03  --bmc1_ucm_cone_mode                    none
% 3.79/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.79/1.03  --bmc1_ucm_relax_model                  4
% 3.79/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.79/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/1.03  --bmc1_ucm_layered_model                none
% 3.79/1.03  --bmc1_ucm_max_lemma_size               10
% 3.79/1.03  
% 3.79/1.03  ------ AIG Options
% 3.79/1.03  
% 3.79/1.03  --aig_mode                              false
% 3.79/1.03  
% 3.79/1.03  ------ Instantiation Options
% 3.79/1.03  
% 3.79/1.03  --instantiation_flag                    true
% 3.79/1.03  --inst_sos_flag                         false
% 3.79/1.03  --inst_sos_phase                        true
% 3.79/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/1.03  --inst_lit_sel_side                     none
% 3.79/1.03  --inst_solver_per_active                1400
% 3.79/1.03  --inst_solver_calls_frac                1.
% 3.79/1.03  --inst_passive_queue_type               priority_queues
% 3.79/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/1.03  --inst_passive_queues_freq              [25;2]
% 3.79/1.03  --inst_dismatching                      true
% 3.79/1.03  --inst_eager_unprocessed_to_passive     true
% 3.79/1.03  --inst_prop_sim_given                   true
% 3.79/1.03  --inst_prop_sim_new                     false
% 3.79/1.03  --inst_subs_new                         false
% 3.79/1.03  --inst_eq_res_simp                      false
% 3.79/1.03  --inst_subs_given                       false
% 3.79/1.03  --inst_orphan_elimination               true
% 3.79/1.03  --inst_learning_loop_flag               true
% 3.79/1.03  --inst_learning_start                   3000
% 3.79/1.03  --inst_learning_factor                  2
% 3.79/1.03  --inst_start_prop_sim_after_learn       3
% 3.79/1.03  --inst_sel_renew                        solver
% 3.79/1.03  --inst_lit_activity_flag                true
% 3.79/1.03  --inst_restr_to_given                   false
% 3.79/1.03  --inst_activity_threshold               500
% 3.79/1.03  --inst_out_proof                        true
% 3.79/1.03  
% 3.79/1.03  ------ Resolution Options
% 3.79/1.03  
% 3.79/1.03  --resolution_flag                       false
% 3.79/1.03  --res_lit_sel                           adaptive
% 3.79/1.03  --res_lit_sel_side                      none
% 3.79/1.03  --res_ordering                          kbo
% 3.79/1.03  --res_to_prop_solver                    active
% 3.79/1.03  --res_prop_simpl_new                    false
% 3.79/1.03  --res_prop_simpl_given                  true
% 3.79/1.03  --res_passive_queue_type                priority_queues
% 3.79/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/1.03  --res_passive_queues_freq               [15;5]
% 3.79/1.03  --res_forward_subs                      full
% 3.79/1.03  --res_backward_subs                     full
% 3.79/1.03  --res_forward_subs_resolution           true
% 3.79/1.03  --res_backward_subs_resolution          true
% 3.79/1.03  --res_orphan_elimination                true
% 3.79/1.03  --res_time_limit                        2.
% 3.79/1.03  --res_out_proof                         true
% 3.79/1.03  
% 3.79/1.03  ------ Superposition Options
% 3.79/1.03  
% 3.79/1.03  --superposition_flag                    true
% 3.79/1.03  --sup_passive_queue_type                priority_queues
% 3.79/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.79/1.03  --demod_completeness_check              fast
% 3.79/1.03  --demod_use_ground                      true
% 3.79/1.03  --sup_to_prop_solver                    passive
% 3.79/1.03  --sup_prop_simpl_new                    true
% 3.79/1.03  --sup_prop_simpl_given                  true
% 3.79/1.03  --sup_fun_splitting                     false
% 3.79/1.03  --sup_smt_interval                      50000
% 3.79/1.03  
% 3.79/1.03  ------ Superposition Simplification Setup
% 3.79/1.03  
% 3.79/1.03  --sup_indices_passive                   []
% 3.79/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.03  --sup_full_bw                           [BwDemod]
% 3.79/1.03  --sup_immed_triv                        [TrivRules]
% 3.79/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.03  --sup_immed_bw_main                     []
% 3.79/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/1.03  
% 3.79/1.03  ------ Combination Options
% 3.79/1.03  
% 3.79/1.03  --comb_res_mult                         3
% 3.79/1.03  --comb_sup_mult                         2
% 3.79/1.03  --comb_inst_mult                        10
% 3.79/1.03  
% 3.79/1.03  ------ Debug Options
% 3.79/1.03  
% 3.79/1.03  --dbg_backtrace                         false
% 3.79/1.03  --dbg_dump_prop_clauses                 false
% 3.79/1.03  --dbg_dump_prop_clauses_file            -
% 3.79/1.03  --dbg_out_stat                          false
% 3.79/1.03  
% 3.79/1.03  
% 3.79/1.03  
% 3.79/1.03  
% 3.79/1.03  ------ Proving...
% 3.79/1.03  
% 3.79/1.03  
% 3.79/1.03  % SZS status Theorem for theBenchmark.p
% 3.79/1.03  
% 3.79/1.03   Resolution empty clause
% 3.79/1.03  
% 3.79/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/1.03  
% 3.79/1.03  fof(f14,conjecture,(
% 3.79/1.03    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f15,negated_conjecture,(
% 3.79/1.03    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.79/1.03    inference(negated_conjecture,[],[f14])).
% 3.79/1.03  
% 3.79/1.03  fof(f26,plain,(
% 3.79/1.03    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.79/1.03    inference(ennf_transformation,[],[f15])).
% 3.79/1.03  
% 3.79/1.03  fof(f27,plain,(
% 3.79/1.03    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.79/1.03    inference(flattening,[],[f26])).
% 3.79/1.03  
% 3.79/1.03  fof(f34,plain,(
% 3.79/1.03    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 3.79/1.03    introduced(choice_axiom,[])).
% 3.79/1.03  
% 3.79/1.03  fof(f35,plain,(
% 3.79/1.03    k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 3.79/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f27,f34])).
% 3.79/1.03  
% 3.79/1.03  fof(f60,plain,(
% 3.79/1.03    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 3.79/1.03    inference(cnf_transformation,[],[f35])).
% 3.79/1.03  
% 3.79/1.03  fof(f6,axiom,(
% 3.79/1.03    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f41,plain,(
% 3.79/1.03    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.79/1.03    inference(cnf_transformation,[],[f6])).
% 3.79/1.03  
% 3.79/1.03  fof(f76,plain,(
% 3.79/1.03    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 3.79/1.03    inference(definition_unfolding,[],[f60,f41])).
% 3.79/1.03  
% 3.79/1.03  fof(f4,axiom,(
% 3.79/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f20,plain,(
% 3.79/1.03    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.79/1.03    inference(ennf_transformation,[],[f4])).
% 3.79/1.03  
% 3.79/1.03  fof(f21,plain,(
% 3.79/1.03    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.79/1.03    inference(flattening,[],[f20])).
% 3.79/1.03  
% 3.79/1.03  fof(f39,plain,(
% 3.79/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.79/1.03    inference(cnf_transformation,[],[f21])).
% 3.79/1.03  
% 3.79/1.03  fof(f2,axiom,(
% 3.79/1.03    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f18,plain,(
% 3.79/1.03    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.79/1.03    inference(ennf_transformation,[],[f2])).
% 3.79/1.03  
% 3.79/1.03  fof(f28,plain,(
% 3.79/1.03    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK0(X0),sK1(X0)) = X0)),
% 3.79/1.03    introduced(choice_axiom,[])).
% 3.79/1.03  
% 3.79/1.03  fof(f29,plain,(
% 3.79/1.03    ! [X0,X1,X2] : (k4_tarski(sK0(X0),sK1(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.79/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f28])).
% 3.79/1.03  
% 3.79/1.03  fof(f37,plain,(
% 3.79/1.03    ( ! [X2,X0,X1] : (k4_tarski(sK0(X0),sK1(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.79/1.03    inference(cnf_transformation,[],[f29])).
% 3.79/1.03  
% 3.79/1.03  fof(f10,axiom,(
% 3.79/1.03    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f24,plain,(
% 3.79/1.03    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.79/1.03    inference(ennf_transformation,[],[f10])).
% 3.79/1.03  
% 3.79/1.03  fof(f30,plain,(
% 3.79/1.03    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 3.79/1.03    introduced(choice_axiom,[])).
% 3.79/1.03  
% 3.79/1.03  fof(f31,plain,(
% 3.79/1.03    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 3.79/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f30])).
% 3.79/1.03  
% 3.79/1.03  fof(f47,plain,(
% 3.79/1.03    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.79/1.03    inference(cnf_transformation,[],[f31])).
% 3.79/1.03  
% 3.79/1.03  fof(f1,axiom,(
% 3.79/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f16,plain,(
% 3.79/1.03    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.79/1.03    inference(unused_predicate_definition_removal,[],[f1])).
% 3.79/1.03  
% 3.79/1.03  fof(f17,plain,(
% 3.79/1.03    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.79/1.03    inference(ennf_transformation,[],[f16])).
% 3.79/1.03  
% 3.79/1.03  fof(f36,plain,(
% 3.79/1.03    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.79/1.03    inference(cnf_transformation,[],[f17])).
% 3.79/1.03  
% 3.79/1.03  fof(f11,axiom,(
% 3.79/1.03    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f25,plain,(
% 3.79/1.03    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.79/1.03    inference(ennf_transformation,[],[f11])).
% 3.79/1.03  
% 3.79/1.03  fof(f51,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.79/1.03    inference(cnf_transformation,[],[f25])).
% 3.79/1.03  
% 3.79/1.03  fof(f68,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.79/1.03    inference(definition_unfolding,[],[f51,f41])).
% 3.79/1.03  
% 3.79/1.03  fof(f12,axiom,(
% 3.79/1.03    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f32,plain,(
% 3.79/1.03    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.79/1.03    inference(nnf_transformation,[],[f12])).
% 3.79/1.03  
% 3.79/1.03  fof(f33,plain,(
% 3.79/1.03    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.79/1.03    inference(flattening,[],[f32])).
% 3.79/1.03  
% 3.79/1.03  fof(f56,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 3.79/1.03    inference(cnf_transformation,[],[f33])).
% 3.79/1.03  
% 3.79/1.03  fof(f7,axiom,(
% 3.79/1.03    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f42,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.79/1.03    inference(cnf_transformation,[],[f7])).
% 3.79/1.03  
% 3.79/1.03  fof(f66,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.79/1.03    inference(definition_unfolding,[],[f42,f41])).
% 3.79/1.03  
% 3.79/1.03  fof(f71,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 3.79/1.03    inference(definition_unfolding,[],[f56,f66])).
% 3.79/1.03  
% 3.79/1.03  fof(f80,plain,(
% 3.79/1.03    ( ! [X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) = k1_xboole_0) )),
% 3.79/1.03    inference(equality_resolution,[],[f71])).
% 3.79/1.03  
% 3.79/1.03  fof(f62,plain,(
% 3.79/1.03    k1_xboole_0 != sK3),
% 3.79/1.03    inference(cnf_transformation,[],[f35])).
% 3.79/1.03  
% 3.79/1.03  fof(f63,plain,(
% 3.79/1.03    k1_xboole_0 != sK4),
% 3.79/1.03    inference(cnf_transformation,[],[f35])).
% 3.79/1.03  
% 3.79/1.03  fof(f64,plain,(
% 3.79/1.03    k1_xboole_0 != sK5),
% 3.79/1.03    inference(cnf_transformation,[],[f35])).
% 3.79/1.03  
% 3.79/1.03  fof(f53,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.79/1.03    inference(cnf_transformation,[],[f33])).
% 3.79/1.03  
% 3.79/1.03  fof(f74,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.79/1.03    inference(definition_unfolding,[],[f53,f66])).
% 3.79/1.03  
% 3.79/1.03  fof(f54,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 3.79/1.03    inference(cnf_transformation,[],[f33])).
% 3.79/1.03  
% 3.79/1.03  fof(f73,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 3.79/1.03    inference(definition_unfolding,[],[f54,f66])).
% 3.79/1.03  
% 3.79/1.03  fof(f82,plain,(
% 3.79/1.03    ( ! [X2,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0) )),
% 3.79/1.03    inference(equality_resolution,[],[f73])).
% 3.79/1.03  
% 3.79/1.03  fof(f8,axiom,(
% 3.79/1.03    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f22,plain,(
% 3.79/1.03    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.79/1.03    inference(ennf_transformation,[],[f8])).
% 3.79/1.03  
% 3.79/1.03  fof(f44,plain,(
% 3.79/1.03    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.79/1.03    inference(cnf_transformation,[],[f22])).
% 3.79/1.03  
% 3.79/1.03  fof(f55,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 3.79/1.03    inference(cnf_transformation,[],[f33])).
% 3.79/1.03  
% 3.79/1.03  fof(f72,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 3.79/1.03    inference(definition_unfolding,[],[f55,f66])).
% 3.79/1.03  
% 3.79/1.03  fof(f81,plain,(
% 3.79/1.03    ( ! [X2,X0,X3] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3) = k1_xboole_0) )),
% 3.79/1.03    inference(equality_resolution,[],[f72])).
% 3.79/1.03  
% 3.79/1.03  fof(f50,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.79/1.03    inference(cnf_transformation,[],[f25])).
% 3.79/1.03  
% 3.79/1.03  fof(f69,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.79/1.03    inference(definition_unfolding,[],[f50,f41])).
% 3.79/1.03  
% 3.79/1.03  fof(f13,axiom,(
% 3.79/1.03    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f59,plain,(
% 3.79/1.03    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.79/1.03    inference(cnf_transformation,[],[f13])).
% 3.79/1.03  
% 3.79/1.03  fof(f9,axiom,(
% 3.79/1.03    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f23,plain,(
% 3.79/1.03    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 3.79/1.03    inference(ennf_transformation,[],[f9])).
% 3.79/1.03  
% 3.79/1.03  fof(f46,plain,(
% 3.79/1.03    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 3.79/1.03    inference(cnf_transformation,[],[f23])).
% 3.79/1.03  
% 3.79/1.03  fof(f77,plain,(
% 3.79/1.03    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 3.79/1.03    inference(equality_resolution,[],[f46])).
% 3.79/1.03  
% 3.79/1.03  fof(f3,axiom,(
% 3.79/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f19,plain,(
% 3.79/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.79/1.03    inference(ennf_transformation,[],[f3])).
% 3.79/1.03  
% 3.79/1.03  fof(f38,plain,(
% 3.79/1.03    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.79/1.03    inference(cnf_transformation,[],[f19])).
% 3.79/1.03  
% 3.79/1.03  fof(f52,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.79/1.03    inference(cnf_transformation,[],[f25])).
% 3.79/1.03  
% 3.79/1.03  fof(f67,plain,(
% 3.79/1.03    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.79/1.03    inference(definition_unfolding,[],[f52,f41])).
% 3.79/1.03  
% 3.79/1.03  fof(f65,plain,(
% 3.79/1.03    k7_mcart_1(sK3,sK4,sK5,sK7) != sK6),
% 3.79/1.03    inference(cnf_transformation,[],[f35])).
% 3.79/1.03  
% 3.79/1.03  fof(f58,plain,(
% 3.79/1.03    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.79/1.03    inference(cnf_transformation,[],[f13])).
% 3.79/1.03  
% 3.79/1.03  fof(f43,plain,(
% 3.79/1.03    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.79/1.03    inference(cnf_transformation,[],[f22])).
% 3.79/1.03  
% 3.79/1.03  fof(f61,plain,(
% 3.79/1.03    ( ! [X6,X7,X5] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 3.79/1.03    inference(cnf_transformation,[],[f35])).
% 3.79/1.03  
% 3.79/1.03  fof(f5,axiom,(
% 3.79/1.03    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 3.79/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.03  
% 3.79/1.03  fof(f40,plain,(
% 3.79/1.03    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 3.79/1.03    inference(cnf_transformation,[],[f5])).
% 3.79/1.03  
% 3.79/1.03  fof(f75,plain,(
% 3.79/1.03    ( ! [X6,X7,X5] : (sK6 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 3.79/1.03    inference(definition_unfolding,[],[f61,f40])).
% 3.79/1.03  
% 3.79/1.03  cnf(c_26,negated_conjecture,
% 3.79/1.03      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 3.79/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_453,plain,
% 3.79/1.03      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.79/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_3,plain,
% 3.79/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.79/1.03      inference(cnf_transformation,[],[f39]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_463,plain,
% 3.79/1.03      ( m1_subset_1(X0,X1) != iProver_top
% 3.79/1.03      | r2_hidden(X0,X1) = iProver_top
% 3.79/1.03      | v1_xboole_0(X1) = iProver_top ),
% 3.79/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2780,plain,
% 3.79/1.03      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top
% 3.79/1.03      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_453,c_463]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_1,plain,
% 3.79/1.03      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK0(X0),sK1(X0)) = X0 ),
% 3.79/1.03      inference(cnf_transformation,[],[f37]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_465,plain,
% 3.79/1.03      ( k4_tarski(sK0(X0),sK1(X0)) = X0
% 3.79/1.03      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.79/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2792,plain,
% 3.79/1.03      ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7
% 3.79/1.03      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2780,c_465]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_10,plain,
% 3.79/1.03      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.79/1.03      inference(cnf_transformation,[],[f47]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_458,plain,
% 3.79/1.03      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.79/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_0,plain,
% 3.79/1.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.79/1.03      inference(cnf_transformation,[],[f36]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_466,plain,
% 3.79/1.03      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.79/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2150,plain,
% 3.79/1.03      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_458,c_466]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2826,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(sK7),sK1(sK7)) = sK7 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2792,c_2150]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_12,plain,
% 3.79/1.03      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.79/1.03      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.79/1.03      | k1_xboole_0 = X1
% 3.79/1.03      | k1_xboole_0 = X2
% 3.79/1.03      | k1_xboole_0 = X3 ),
% 3.79/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_456,plain,
% 3.79/1.03      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.79/1.03      | k1_xboole_0 = X0
% 3.79/1.03      | k1_xboole_0 = X1
% 3.79/1.03      | k1_xboole_0 = X2
% 3.79/1.03      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.79/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_3197,plain,
% 3.79/1.03      ( k6_mcart_1(k2_zfmisc_1(sK3,sK4),sK5,X0,X1) = k2_mcart_1(k1_mcart_1(X1))
% 3.79/1.03      | k2_zfmisc_1(sK3,sK4) = k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(sK7),sK1(sK7)) = sK7
% 3.79/1.03      | sK5 = k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = X0
% 3.79/1.03      | m1_subset_1(X1,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2826,c_456]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_15,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
% 3.79/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_907,plain,
% 3.79/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_15,c_15]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_3299,plain,
% 3.79/1.03      ( k6_mcart_1(k2_zfmisc_1(sK3,sK4),sK5,X0,X1) = k2_mcart_1(k1_mcart_1(X1))
% 3.79/1.03      | k2_zfmisc_1(sK3,sK4) = k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(sK7),sK1(sK7)) = sK7
% 3.79/1.03      | sK5 = k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = X0
% 3.79/1.03      | m1_subset_1(X1,k1_xboole_0) != iProver_top ),
% 3.79/1.03      inference(light_normalisation,[status(thm)],[c_3197,c_907]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_24,negated_conjecture,
% 3.79/1.03      ( k1_xboole_0 != sK3 ),
% 3.79/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_23,negated_conjecture,
% 3.79/1.03      ( k1_xboole_0 != sK4 ),
% 3.79/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_22,negated_conjecture,
% 3.79/1.03      ( k1_xboole_0 != sK5 ),
% 3.79/1.03      inference(cnf_transformation,[],[f64]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_18,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = X0
% 3.79/1.03      | k1_xboole_0 = X1
% 3.79/1.03      | k1_xboole_0 = X2
% 3.79/1.03      | k1_xboole_0 = X3 ),
% 3.79/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_33,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = k1_xboole_0 ),
% 3.79/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_17,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 3.79/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_34,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.79/1.03      inference(instantiation,[status(thm)],[c_17]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_202,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_638,plain,
% 3.79/1.03      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.79/1.03      inference(instantiation,[status(thm)],[c_202]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_639,plain,
% 3.79/1.03      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 3.79/1.03      inference(instantiation,[status(thm)],[c_638]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_640,plain,
% 3.79/1.03      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.79/1.03      inference(instantiation,[status(thm)],[c_202]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_641,plain,
% 3.79/1.03      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 3.79/1.03      inference(instantiation,[status(thm)],[c_640]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_642,plain,
% 3.79/1.03      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.79/1.03      inference(instantiation,[status(thm)],[c_202]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_643,plain,
% 3.79/1.03      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 3.79/1.03      inference(instantiation,[status(thm)],[c_642]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_3207,plain,
% 3.79/1.03      ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7
% 3.79/1.03      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2826,c_2792]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_4,plain,
% 3.79/1.03      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.79/1.03      inference(cnf_transformation,[],[f44]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_462,plain,
% 3.79/1.03      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.79/1.03      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.79/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2581,plain,
% 3.79/1.03      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.79/1.03      | r2_hidden(k2_mcart_1(sK2(k2_zfmisc_1(X0,X1))),X1) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_458,c_462]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_10384,plain,
% 3.79/1.03      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | v1_xboole_0(X1) != iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2581,c_466]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_10439,plain,
% 3.79/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(sK7),sK1(sK7)) = sK7 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_3207,c_10384]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_3210,plain,
% 3.79/1.03      ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7
% 3.79/1.03      | m1_subset_1(sK7,k1_xboole_0) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2826,c_453]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_16,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1),X2) = k1_xboole_0 ),
% 3.79/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_13,plain,
% 3.79/1.03      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.79/1.03      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.79/1.03      | k1_xboole_0 = X1
% 3.79/1.03      | k1_xboole_0 = X2
% 3.79/1.03      | k1_xboole_0 = X3 ),
% 3.79/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_455,plain,
% 3.79/1.03      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.79/1.03      | k1_xboole_0 = X0
% 3.79/1.03      | k1_xboole_0 = X1
% 3.79/1.03      | k1_xboole_0 = X2
% 3.79/1.03      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.79/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_932,plain,
% 3.79/1.03      ( k5_mcart_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1),X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
% 3.79/1.03      | k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = X3
% 3.79/1.03      | k1_xboole_0 = X2
% 3.79/1.03      | m1_subset_1(X4,k2_zfmisc_1(k1_xboole_0,X3)) != iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_16,c_455]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_3987,plain,
% 3.79/1.03      ( k5_mcart_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1),X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
% 3.79/1.03      | k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = X2
% 3.79/1.03      | k1_xboole_0 = X3
% 3.79/1.03      | m1_subset_1(X4,k1_xboole_0) != iProver_top ),
% 3.79/1.03      inference(demodulation,[status(thm)],[c_932,c_907]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_3994,plain,
% 3.79/1.03      ( k5_mcart_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1),X2,X3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 3.79/1.03      | k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X1) = k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(sK7),sK1(sK7)) = sK7
% 3.79/1.03      | k1_xboole_0 = X2
% 3.79/1.03      | k1_xboole_0 = X3 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_3210,c_3987]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_11927,plain,
% 3.79/1.03      ( k5_mcart_1(k2_zfmisc_1(k1_xboole_0,X0),X1,X2,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 3.79/1.03      | k2_zfmisc_1(k2_zfmisc_1(X3,k1_xboole_0),X0) = k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(sK7),sK1(sK7)) = sK7
% 3.79/1.03      | k1_xboole_0 = X1
% 3.79/1.03      | k1_xboole_0 = X2 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_10439,c_3994]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_11941,plain,
% 3.79/1.03      ( k5_mcart_1(k1_xboole_0,X0,X1,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 3.79/1.03      | k2_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0),X3) = k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(sK7),sK1(sK7)) = sK7
% 3.79/1.03      | k1_xboole_0 = X0
% 3.79/1.03      | k1_xboole_0 = X1 ),
% 3.79/1.03      inference(light_normalisation,[status(thm)],[c_11927,c_907]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_3202,plain,
% 3.79/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(sK7),sK1(sK7)) = sK7
% 3.79/1.03      | sK5 = k1_xboole_0
% 3.79/1.03      | sK4 = k1_xboole_0
% 3.79/1.03      | sK3 = k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = X0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2826,c_18]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_3258,plain,
% 3.79/1.03      ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7
% 3.79/1.03      | sK5 = k1_xboole_0
% 3.79/1.03      | sK4 = k1_xboole_0
% 3.79/1.03      | sK3 = k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = X0
% 3.79/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 3.79/1.03      inference(light_normalisation,[status(thm)],[c_3202,c_907]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_3259,plain,
% 3.79/1.03      ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7
% 3.79/1.03      | sK5 = k1_xboole_0
% 3.79/1.03      | sK4 = k1_xboole_0
% 3.79/1.03      | sK3 = k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = X0 ),
% 3.79/1.03      inference(equality_resolution_simp,[status(thm)],[c_3258]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_16908,plain,
% 3.79/1.03      ( k1_xboole_0 = X0 | k4_tarski(sK0(sK7),sK1(sK7)) = sK7 ),
% 3.79/1.03      inference(global_propositional_subsumption,
% 3.79/1.03                [status(thm)],
% 3.79/1.03                [c_11941,c_24,c_23,c_22,c_33,c_34,c_639,c_641,c_643,c_3259]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_16909,plain,
% 3.79/1.03      ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7 | k1_xboole_0 = X0 ),
% 3.79/1.03      inference(renaming,[status(thm)],[c_16908]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_19,plain,
% 3.79/1.03      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.79/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_17269,plain,
% 3.79/1.03      ( k2_mcart_1(sK7) = sK1(sK7) | k1_xboole_0 = X0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_16909,c_19]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_6,plain,
% 3.79/1.03      ( k2_mcart_1(k4_tarski(X0,X1)) != k4_tarski(X0,X1) ),
% 3.79/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_492,plain,
% 3.79/1.03      ( k4_tarski(X0,X1) != X1 ),
% 3.79/1.03      inference(light_normalisation,[status(thm)],[c_6,c_19]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_18540,plain,
% 3.79/1.03      ( k2_mcart_1(sK7) = sK1(sK7) | k1_xboole_0 != X0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_17269,c_492]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_18713,plain,
% 3.79/1.03      ( k2_mcart_1(sK7) = sK1(sK7) ),
% 3.79/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_18540,c_17269]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2793,plain,
% 3.79/1.03      ( r2_hidden(k2_mcart_1(sK7),sK5) = iProver_top
% 3.79/1.03      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2780,c_462]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2821,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | r2_hidden(k2_mcart_1(sK7),sK5) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2793,c_2150]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2,plain,
% 3.79/1.03      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.79/1.03      inference(cnf_transformation,[],[f38]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_464,plain,
% 3.79/1.03      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 3.79/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2872,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | m1_subset_1(k2_mcart_1(sK7),sK5) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2821,c_464]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_19103,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | m1_subset_1(sK1(sK7),sK5) = iProver_top ),
% 3.79/1.03      inference(demodulation,[status(thm)],[c_18713,c_2872]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_11,plain,
% 3.79/1.03      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.79/1.03      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.79/1.03      | k1_xboole_0 = X1
% 3.79/1.03      | k1_xboole_0 = X2
% 3.79/1.03      | k1_xboole_0 = X3 ),
% 3.79/1.03      inference(cnf_transformation,[],[f67]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_457,plain,
% 3.79/1.03      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.79/1.03      | k1_xboole_0 = X0
% 3.79/1.03      | k1_xboole_0 = X1
% 3.79/1.03      | k1_xboole_0 = X2
% 3.79/1.03      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.79/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2654,plain,
% 3.79/1.03      ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7)
% 3.79/1.03      | sK5 = k1_xboole_0
% 3.79/1.03      | sK4 = k1_xboole_0
% 3.79/1.03      | sK3 = k1_xboole_0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_453,c_457]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2813,plain,
% 3.79/1.03      ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7) ),
% 3.79/1.03      inference(global_propositional_subsumption,
% 3.79/1.03                [status(thm)],
% 3.79/1.03                [c_2654,c_24,c_23,c_22,c_33,c_34,c_639,c_641,c_643]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_21,negated_conjecture,
% 3.79/1.03      ( k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
% 3.79/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2816,plain,
% 3.79/1.03      ( k2_mcart_1(sK7) != sK6 ),
% 3.79/1.03      inference(demodulation,[status(thm)],[c_2813,c_21]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_19107,plain,
% 3.79/1.03      ( sK1(sK7) != sK6 ),
% 3.79/1.03      inference(demodulation,[status(thm)],[c_18713,c_2816]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_17228,plain,
% 3.79/1.03      ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7 | k1_xboole_0 != X0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_16909,c_492]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_17480,plain,
% 3.79/1.03      ( k4_tarski(sK0(sK7),sK1(sK7)) = sK7 ),
% 3.79/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_17228,c_16909]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_20,plain,
% 3.79/1.03      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.79/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_17268,plain,
% 3.79/1.03      ( k1_mcart_1(sK7) = sK0(sK7) | k1_xboole_0 = X0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_16909,c_20]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_17934,plain,
% 3.79/1.03      ( k1_mcart_1(sK7) = sK0(sK7) | k1_xboole_0 != X0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_17268,c_492]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_18162,plain,
% 3.79/1.03      ( k1_mcart_1(sK7) = sK0(sK7) ),
% 3.79/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_17934,c_17268]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_5,plain,
% 3.79/1.03      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.79/1.03      inference(cnf_transformation,[],[f43]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_461,plain,
% 3.79/1.03      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.79/1.03      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.79/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2794,plain,
% 3.79/1.03      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) = iProver_top
% 3.79/1.03      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2780,c_461]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2834,plain,
% 3.79/1.03      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top
% 3.79/1.03      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2794,c_461]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_3461,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2834,c_2150]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_4788,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_3461,c_464]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2832,plain,
% 3.79/1.03      ( k4_tarski(sK0(k1_mcart_1(sK7)),sK1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
% 3.79/1.03      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2794,c_465]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2155,plain,
% 3.79/1.03      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.79/1.03      | r2_hidden(k1_mcart_1(sK2(k2_zfmisc_1(X0,X1))),X0) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_458,c_461]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_8362,plain,
% 3.79/1.03      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2155,c_466]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_8421,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),X0) = k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(k1_mcart_1(sK7)),sK1(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2832,c_8362]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_13634,plain,
% 3.79/1.03      ( k4_tarski(sK0(k1_mcart_1(sK7)),sK1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
% 3.79/1.03      | sK5 = k1_xboole_0
% 3.79/1.03      | sK4 = k1_xboole_0
% 3.79/1.03      | sK3 = k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = X0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_8421,c_18]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_14113,plain,
% 3.79/1.03      ( k4_tarski(sK0(k1_mcart_1(sK7)),sK1(k1_mcart_1(sK7))) = k1_mcart_1(sK7)
% 3.79/1.03      | k1_xboole_0 = X0 ),
% 3.79/1.03      inference(global_propositional_subsumption,
% 3.79/1.03                [status(thm)],
% 3.79/1.03                [c_13634,c_24,c_23,c_22,c_33,c_34,c_639,c_641,c_643]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_14551,plain,
% 3.79/1.03      ( k1_mcart_1(k1_mcart_1(sK7)) = sK0(k1_mcart_1(sK7)) | k1_xboole_0 = X0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_14113,c_20]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_15252,plain,
% 3.79/1.03      ( k1_mcart_1(k1_mcart_1(sK7)) = sK0(k1_mcart_1(sK7))
% 3.79/1.03      | k1_xboole_0 != X0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_14551,c_492]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_15413,plain,
% 3.79/1.03      ( k1_mcart_1(k1_mcart_1(sK7)) = sK0(k1_mcart_1(sK7)) ),
% 3.79/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_15252,c_14551]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_16876,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | m1_subset_1(sK0(k1_mcart_1(sK7)),sK3) = iProver_top ),
% 3.79/1.03      inference(light_normalisation,[status(thm)],[c_4788,c_15413]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_18759,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | m1_subset_1(sK0(sK0(sK7)),sK3) = iProver_top ),
% 3.79/1.03      inference(demodulation,[status(thm)],[c_18162,c_16876]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_2833,plain,
% 3.79/1.03      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
% 3.79/1.03      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2794,c_462]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_3448,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2833,c_2150]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_4763,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_3448,c_464]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_14552,plain,
% 3.79/1.03      ( k2_mcart_1(k1_mcart_1(sK7)) = sK1(k1_mcart_1(sK7)) | k1_xboole_0 = X0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_14113,c_19]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_15782,plain,
% 3.79/1.03      ( k2_mcart_1(k1_mcart_1(sK7)) = sK1(k1_mcart_1(sK7))
% 3.79/1.03      | k1_xboole_0 != X0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_14552,c_492]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_15957,plain,
% 3.79/1.03      ( k2_mcart_1(k1_mcart_1(sK7)) = sK1(k1_mcart_1(sK7)) ),
% 3.79/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_15782,c_14552]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_16796,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | m1_subset_1(sK1(k1_mcart_1(sK7)),sK4) = iProver_top ),
% 3.79/1.03      inference(light_normalisation,[status(thm)],[c_4763,c_15957]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_18760,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | m1_subset_1(sK1(sK0(sK7)),sK4) = iProver_top ),
% 3.79/1.03      inference(demodulation,[status(thm)],[c_18162,c_16796]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_4441,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(k1_mcart_1(sK7)),sK1(k1_mcart_1(sK7))) = k1_mcart_1(sK7) ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_2832,c_2150]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_25,negated_conjecture,
% 3.79/1.03      ( ~ m1_subset_1(X0,sK5)
% 3.79/1.03      | ~ m1_subset_1(X1,sK4)
% 3.79/1.03      | ~ m1_subset_1(X2,sK3)
% 3.79/1.03      | k4_tarski(k4_tarski(X2,X1),X0) != sK7
% 3.79/1.03      | sK6 = X0 ),
% 3.79/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_454,plain,
% 3.79/1.03      ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
% 3.79/1.03      | sK6 = X2
% 3.79/1.03      | m1_subset_1(X2,sK5) != iProver_top
% 3.79/1.03      | m1_subset_1(X1,sK4) != iProver_top
% 3.79/1.03      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.79/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_4807,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | k4_tarski(k1_mcart_1(sK7),X0) != sK7
% 3.79/1.03      | sK6 = X0
% 3.79/1.03      | m1_subset_1(X0,sK5) != iProver_top
% 3.79/1.03      | m1_subset_1(sK1(k1_mcart_1(sK7)),sK4) != iProver_top
% 3.79/1.03      | m1_subset_1(sK0(k1_mcart_1(sK7)),sK3) != iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_4441,c_454]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_18776,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(sK7),X0) != sK7
% 3.79/1.03      | sK6 = X0
% 3.79/1.03      | m1_subset_1(X0,sK5) != iProver_top
% 3.79/1.03      | m1_subset_1(sK1(sK0(sK7)),sK4) != iProver_top
% 3.79/1.03      | m1_subset_1(sK0(sK0(sK7)),sK3) != iProver_top ),
% 3.79/1.03      inference(demodulation,[status(thm)],[c_18162,c_4807]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_18880,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(sK7),X0) != sK7
% 3.79/1.03      | sK6 = X0
% 3.79/1.03      | m1_subset_1(X0,sK5) != iProver_top
% 3.79/1.03      | m1_subset_1(sK0(sK0(sK7)),sK3) != iProver_top ),
% 3.79/1.03      inference(backward_subsumption_resolution,
% 3.79/1.03                [status(thm)],
% 3.79/1.03                [c_18760,c_18776]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_18895,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | k4_tarski(sK0(sK7),X0) != sK7
% 3.79/1.03      | sK6 = X0
% 3.79/1.03      | m1_subset_1(X0,sK5) != iProver_top ),
% 3.79/1.03      inference(backward_subsumption_resolution,
% 3.79/1.03                [status(thm)],
% 3.79/1.03                [c_18759,c_18880]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_20051,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 3.79/1.03      | sK1(sK7) = sK6
% 3.79/1.03      | m1_subset_1(sK1(sK7),sK5) != iProver_top ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_17480,c_18895]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_20281,plain,
% 3.79/1.03      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0 ),
% 3.79/1.03      inference(global_propositional_subsumption,
% 3.79/1.03                [status(thm)],
% 3.79/1.03                [c_19103,c_19107,c_20051]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_20381,plain,
% 3.79/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 3.79/1.03      | sK5 = k1_xboole_0
% 3.79/1.03      | sK4 = k1_xboole_0
% 3.79/1.03      | sK3 = k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = X0 ),
% 3.79/1.03      inference(superposition,[status(thm)],[c_20281,c_18]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_20410,plain,
% 3.79/1.03      ( sK5 = k1_xboole_0
% 3.79/1.03      | sK4 = k1_xboole_0
% 3.79/1.03      | sK3 = k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = X0
% 3.79/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 3.79/1.03      inference(light_normalisation,[status(thm)],[c_20381,c_907]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_20411,plain,
% 3.79/1.03      ( sK5 = k1_xboole_0
% 3.79/1.03      | sK4 = k1_xboole_0
% 3.79/1.03      | sK3 = k1_xboole_0
% 3.79/1.03      | k1_xboole_0 = X0 ),
% 3.79/1.03      inference(equality_resolution_simp,[status(thm)],[c_20410]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_20493,plain,
% 3.79/1.03      ( k1_xboole_0 = X0 ),
% 3.79/1.03      inference(global_propositional_subsumption,
% 3.79/1.03                [status(thm)],
% 3.79/1.03                [c_3299,c_24,c_23,c_22,c_33,c_34,c_639,c_641,c_643,c_20411]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_20573,plain,
% 3.79/1.03      ( k1_xboole_0 != k1_xboole_0 ),
% 3.79/1.03      inference(demodulation,[status(thm)],[c_20493,c_23]) ).
% 3.79/1.03  
% 3.79/1.03  cnf(c_20615,plain,
% 3.79/1.03      ( $false ),
% 3.79/1.03      inference(equality_resolution_simp,[status(thm)],[c_20573]) ).
% 3.79/1.03  
% 3.79/1.03  
% 3.79/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/1.03  
% 3.79/1.03  ------                               Statistics
% 3.79/1.03  
% 3.79/1.03  ------ General
% 3.79/1.03  
% 3.79/1.03  abstr_ref_over_cycles:                  0
% 3.79/1.03  abstr_ref_under_cycles:                 0
% 3.79/1.03  gc_basic_clause_elim:                   0
% 3.79/1.03  forced_gc_time:                         0
% 3.79/1.03  parsing_time:                           0.025
% 3.79/1.03  unif_index_cands_time:                  0.
% 3.79/1.03  unif_index_add_time:                    0.
% 3.79/1.03  orderings_time:                         0.
% 3.79/1.03  out_proof_time:                         0.012
% 3.79/1.03  total_time:                             0.501
% 3.79/1.03  num_of_symbols:                         51
% 3.79/1.03  num_of_terms:                           14859
% 3.79/1.03  
% 3.79/1.03  ------ Preprocessing
% 3.79/1.03  
% 3.79/1.03  num_of_splits:                          0
% 3.79/1.03  num_of_split_atoms:                     0
% 3.79/1.03  num_of_reused_defs:                     0
% 3.79/1.03  num_eq_ax_congr_red:                    32
% 3.79/1.03  num_of_sem_filtered_clauses:            1
% 3.79/1.03  num_of_subtypes:                        0
% 3.79/1.03  monotx_restored_types:                  0
% 3.79/1.03  sat_num_of_epr_types:                   0
% 3.79/1.03  sat_num_of_non_cyclic_types:            0
% 3.79/1.03  sat_guarded_non_collapsed_types:        0
% 3.79/1.03  num_pure_diseq_elim:                    0
% 3.79/1.03  simp_replaced_by:                       0
% 3.79/1.03  res_preprocessed:                       100
% 3.79/1.03  prep_upred:                             0
% 3.79/1.03  prep_unflattend:                        0
% 3.79/1.03  smt_new_axioms:                         0
% 3.79/1.03  pred_elim_cands:                        3
% 3.79/1.03  pred_elim:                              0
% 3.79/1.03  pred_elim_cl:                           0
% 3.79/1.03  pred_elim_cycles:                       1
% 3.79/1.03  merged_defs:                            0
% 3.79/1.03  merged_defs_ncl:                        0
% 3.79/1.03  bin_hyper_res:                          0
% 3.79/1.03  prep_cycles:                            3
% 3.79/1.03  pred_elim_time:                         0.
% 3.79/1.03  splitting_time:                         0.
% 3.79/1.03  sem_filter_time:                        0.
% 3.79/1.03  monotx_time:                            0.
% 3.79/1.03  subtype_inf_time:                       0.
% 3.79/1.03  
% 3.79/1.03  ------ Problem properties
% 3.79/1.03  
% 3.79/1.03  clauses:                                27
% 3.79/1.03  conjectures:                            6
% 3.79/1.03  epr:                                    6
% 3.79/1.03  horn:                                   21
% 3.79/1.03  ground:                                 5
% 3.79/1.03  unary:                                  13
% 3.79/1.03  binary:                                 6
% 3.79/1.03  lits:                                   59
% 3.79/1.03  lits_eq:                                37
% 3.79/1.03  fd_pure:                                0
% 3.79/1.03  fd_pseudo:                              0
% 3.79/1.03  fd_cond:                                8
% 3.79/1.03  fd_pseudo_cond:                         0
% 3.79/1.03  ac_symbols:                             0
% 3.79/1.03  
% 3.79/1.03  ------ Propositional Solver
% 3.79/1.03  
% 3.79/1.03  prop_solver_calls:                      25
% 3.79/1.03  prop_fast_solver_calls:                 1311
% 3.79/1.03  smt_solver_calls:                       0
% 3.79/1.03  smt_fast_solver_calls:                  0
% 3.79/1.03  prop_num_of_clauses:                    5921
% 3.79/1.03  prop_preprocess_simplified:             12601
% 3.79/1.03  prop_fo_subsumed:                       114
% 3.79/1.03  prop_solver_time:                       0.
% 3.79/1.03  smt_solver_time:                        0.
% 3.79/1.03  smt_fast_solver_time:                   0.
% 3.79/1.03  prop_fast_solver_time:                  0.
% 3.79/1.03  prop_unsat_core_time:                   0.
% 3.79/1.03  
% 3.79/1.03  ------ QBF
% 3.79/1.03  
% 3.79/1.03  qbf_q_res:                              0
% 3.79/1.03  qbf_num_tautologies:                    0
% 3.79/1.03  qbf_prep_cycles:                        0
% 3.79/1.03  
% 3.79/1.03  ------ BMC1
% 3.79/1.03  
% 3.79/1.03  bmc1_current_bound:                     -1
% 3.79/1.03  bmc1_last_solved_bound:                 -1
% 3.79/1.03  bmc1_unsat_core_size:                   -1
% 3.79/1.03  bmc1_unsat_core_parents_size:           -1
% 3.79/1.03  bmc1_merge_next_fun:                    0
% 3.79/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.79/1.03  
% 3.79/1.03  ------ Instantiation
% 3.79/1.03  
% 3.79/1.03  inst_num_of_clauses:                    1979
% 3.79/1.03  inst_num_in_passive:                    231
% 3.79/1.03  inst_num_in_active:                     1027
% 3.79/1.03  inst_num_in_unprocessed:                721
% 3.79/1.03  inst_num_of_loops:                      1100
% 3.79/1.03  inst_num_of_learning_restarts:          0
% 3.79/1.03  inst_num_moves_active_passive:          72
% 3.79/1.03  inst_lit_activity:                      0
% 3.79/1.03  inst_lit_activity_moves:                0
% 3.79/1.03  inst_num_tautologies:                   0
% 3.79/1.03  inst_num_prop_implied:                  0
% 3.79/1.03  inst_num_existing_simplified:           0
% 3.79/1.03  inst_num_eq_res_simplified:             0
% 3.79/1.03  inst_num_child_elim:                    0
% 3.79/1.03  inst_num_of_dismatching_blockings:      161
% 3.79/1.03  inst_num_of_non_proper_insts:           1201
% 3.79/1.03  inst_num_of_duplicates:                 0
% 3.79/1.03  inst_inst_num_from_inst_to_res:         0
% 3.79/1.03  inst_dismatching_checking_time:         0.
% 3.79/1.03  
% 3.79/1.03  ------ Resolution
% 3.79/1.03  
% 3.79/1.03  res_num_of_clauses:                     0
% 3.79/1.03  res_num_in_passive:                     0
% 3.79/1.03  res_num_in_active:                      0
% 3.79/1.03  res_num_of_loops:                       103
% 3.79/1.03  res_forward_subset_subsumed:            41
% 3.79/1.03  res_backward_subset_subsumed:           0
% 3.79/1.03  res_forward_subsumed:                   0
% 3.79/1.03  res_backward_subsumed:                  0
% 3.79/1.03  res_forward_subsumption_resolution:     0
% 3.79/1.03  res_backward_subsumption_resolution:    0
% 3.79/1.03  res_clause_to_clause_subsumption:       2444
% 3.79/1.03  res_orphan_elimination:                 0
% 3.79/1.03  res_tautology_del:                      17
% 3.79/1.03  res_num_eq_res_simplified:              0
% 3.79/1.03  res_num_sel_changes:                    0
% 3.79/1.03  res_moves_from_active_to_pass:          0
% 3.79/1.03  
% 3.79/1.03  ------ Superposition
% 3.79/1.03  
% 3.79/1.03  sup_time_total:                         0.
% 3.79/1.03  sup_time_generating:                    0.
% 3.79/1.03  sup_time_sim_full:                      0.
% 3.79/1.03  sup_time_sim_immed:                     0.
% 3.79/1.03  
% 3.79/1.03  sup_num_of_clauses:                     253
% 3.79/1.03  sup_num_in_active:                      6
% 3.79/1.03  sup_num_in_passive:                     247
% 3.79/1.03  sup_num_of_loops:                       219
% 3.79/1.03  sup_fw_superposition:                   490
% 3.79/1.03  sup_bw_superposition:                   4454
% 3.79/1.03  sup_immediate_simplified:               2724
% 3.79/1.03  sup_given_eliminated:                   0
% 3.79/1.03  comparisons_done:                       0
% 3.79/1.03  comparisons_avoided:                    173
% 3.79/1.03  
% 3.79/1.03  ------ Simplifications
% 3.79/1.03  
% 3.79/1.03  
% 3.79/1.03  sim_fw_subset_subsumed:                 2111
% 3.79/1.03  sim_bw_subset_subsumed:                 222
% 3.79/1.03  sim_fw_subsumed:                        419
% 3.79/1.03  sim_bw_subsumed:                        21
% 3.79/1.03  sim_fw_subsumption_res:                 9
% 3.79/1.03  sim_bw_subsumption_res:                 2
% 3.79/1.03  sim_tautology_del:                      27
% 3.79/1.03  sim_eq_tautology_del:                   129
% 3.79/1.03  sim_eq_res_simp:                        36
% 3.79/1.03  sim_fw_demodulated:                     59
% 3.79/1.03  sim_bw_demodulated:                     190
% 3.79/1.03  sim_light_normalised:                   59
% 3.79/1.03  sim_joinable_taut:                      0
% 3.79/1.03  sim_joinable_simp:                      0
% 3.79/1.03  sim_ac_normalised:                      0
% 3.79/1.03  sim_smt_subsumption:                    0
% 3.79/1.03  
%------------------------------------------------------------------------------
