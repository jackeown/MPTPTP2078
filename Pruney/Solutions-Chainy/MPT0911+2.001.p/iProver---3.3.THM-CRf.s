%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:00 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 819 expanded)
%              Number of clauses        :   76 ( 237 expanded)
%              Number of leaves         :   16 ( 193 expanded)
%              Depth                    :   22
%              Number of atoms          :  467 (4097 expanded)
%              Number of equality atoms :  336 (2853 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f63,f73])).

fof(f91,plain,(
    ! [X2,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f82])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f62,f73])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
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
    inference(flattening,[],[f28])).

fof(f38,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f29,f38])).

fof(f69,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f67,f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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

fof(f35,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f34])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f58,f49,f50])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f59,f50])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f60,f50])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f61,f50])).

fof(f68,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X7
      | k3_mcart_1(X5,X6,X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(definition_unfolding,[],[f68,f49])).

fof(f72,plain,(
    k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f89,plain,(
    ! [X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f80])).

cnf(c_22,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_23,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1519,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(superposition,[status(thm)],[c_22,c_23])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_34,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_35,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_418,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1005,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_1006,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_1007,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_1008,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_1009,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_1010,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_768,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_780,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2498,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_780])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_777,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2630,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2498,c_777])).

cnf(c_3115,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2630,c_777])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_774,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_787,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2248,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_787])).

cnf(c_3662,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3115,c_2248])).

cnf(c_3730,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3662,c_787])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_781,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3731,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3662,c_781])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_773,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3748,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK7),k6_mcart_1(sK3,sK4,sK5,sK7)),k7_mcart_1(sK3,sK4,sK5,sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_768,c_773])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_770,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1242,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_768,c_770])).

cnf(c_1574,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1242,c_27,c_26,c_25,c_34,c_35,c_1006,c_1008,c_1010])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_771,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2041,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_768,c_771])).

cnf(c_2641,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2041,c_27,c_26,c_25,c_34,c_35,c_1006,c_1008,c_1010])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_772,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3510,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_768,c_772])).

cnf(c_3654,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3510,c_27,c_26,c_25,c_34,c_35,c_1006,c_1008,c_1010])).

cnf(c_3793,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))),k2_mcart_1(sK7)) = sK7
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3748,c_1574,c_2641,c_3654])).

cnf(c_3990,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))),k2_mcart_1(sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3793,c_27,c_26,c_25,c_34,c_35,c_1006,c_1008,c_1010])).

cnf(c_28,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ m1_subset_1(X1,sK4)
    | ~ m1_subset_1(X2,sK3)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK7
    | sK6 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_769,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
    | sK6 = X2
    | m1_subset_1(X2,sK5) != iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3994,plain,
    ( k2_mcart_1(sK7) = sK6
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
    | m1_subset_1(k2_mcart_1(sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3990,c_769])).

cnf(c_24,negated_conjecture,
    ( k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3657,plain,
    ( k2_mcart_1(sK7) != sK6 ),
    inference(demodulation,[status(thm)],[c_3654,c_24])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_779,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3803,plain,
    ( m1_subset_1(k7_mcart_1(sK3,sK4,sK5,sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_768,c_779])).

cnf(c_3850,plain,
    ( m1_subset_1(k2_mcart_1(sK7),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3803,c_3654])).

cnf(c_4043,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3994,c_3657,c_3850])).

cnf(c_4044,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4043])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_778,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3114,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2630,c_778])).

cnf(c_3663,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3114,c_2248])).

cnf(c_4067,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3663,c_781])).

cnf(c_4291,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3730,c_3731,c_4044,c_4067])).

cnf(c_4358,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_4291,c_23])).

cnf(c_20,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1263,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20,c_20])).

cnf(c_4376,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4358,c_1263])).

cnf(c_4377,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4376])).

cnf(c_5274,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1519,c_27,c_26,c_25,c_34,c_35,c_1006,c_1008,c_1010,c_4377])).

cnf(c_5306,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5274,c_25])).

cnf(c_5323,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5306])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.75/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/0.98  
% 2.75/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.75/0.98  
% 2.75/0.98  ------  iProver source info
% 2.75/0.98  
% 2.75/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.75/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.75/0.98  git: non_committed_changes: false
% 2.75/0.98  git: last_make_outside_of_git: false
% 2.75/0.98  
% 2.75/0.98  ------ 
% 2.75/0.98  
% 2.75/0.98  ------ Input Options
% 2.75/0.98  
% 2.75/0.98  --out_options                           all
% 2.75/0.98  --tptp_safe_out                         true
% 2.75/0.98  --problem_path                          ""
% 2.75/0.98  --include_path                          ""
% 2.75/0.98  --clausifier                            res/vclausify_rel
% 2.75/0.98  --clausifier_options                    --mode clausify
% 2.75/0.98  --stdin                                 false
% 2.75/0.98  --stats_out                             all
% 2.75/0.98  
% 2.75/0.98  ------ General Options
% 2.75/0.98  
% 2.75/0.98  --fof                                   false
% 2.75/0.98  --time_out_real                         305.
% 2.75/0.98  --time_out_virtual                      -1.
% 2.75/0.98  --symbol_type_check                     false
% 2.75/0.98  --clausify_out                          false
% 2.75/0.98  --sig_cnt_out                           false
% 2.75/0.98  --trig_cnt_out                          false
% 2.75/0.98  --trig_cnt_out_tolerance                1.
% 2.75/0.98  --trig_cnt_out_sk_spl                   false
% 2.75/0.98  --abstr_cl_out                          false
% 2.75/0.98  
% 2.75/0.98  ------ Global Options
% 2.75/0.98  
% 2.75/0.98  --schedule                              default
% 2.75/0.98  --add_important_lit                     false
% 2.75/0.98  --prop_solver_per_cl                    1000
% 2.75/0.98  --min_unsat_core                        false
% 2.75/0.98  --soft_assumptions                      false
% 2.75/0.98  --soft_lemma_size                       3
% 2.75/0.98  --prop_impl_unit_size                   0
% 2.75/0.98  --prop_impl_unit                        []
% 2.75/0.98  --share_sel_clauses                     true
% 2.75/0.98  --reset_solvers                         false
% 2.75/0.98  --bc_imp_inh                            [conj_cone]
% 2.75/0.98  --conj_cone_tolerance                   3.
% 2.75/0.98  --extra_neg_conj                        none
% 2.75/0.98  --large_theory_mode                     true
% 2.75/0.98  --prolific_symb_bound                   200
% 2.75/0.98  --lt_threshold                          2000
% 2.75/0.98  --clause_weak_htbl                      true
% 2.75/0.98  --gc_record_bc_elim                     false
% 2.75/0.98  
% 2.75/0.98  ------ Preprocessing Options
% 2.75/0.98  
% 2.75/0.98  --preprocessing_flag                    true
% 2.75/0.98  --time_out_prep_mult                    0.1
% 2.75/0.98  --splitting_mode                        input
% 2.75/0.98  --splitting_grd                         true
% 2.75/0.98  --splitting_cvd                         false
% 2.75/0.98  --splitting_cvd_svl                     false
% 2.75/0.98  --splitting_nvd                         32
% 2.75/0.98  --sub_typing                            true
% 2.75/0.98  --prep_gs_sim                           true
% 2.75/0.98  --prep_unflatten                        true
% 2.75/0.98  --prep_res_sim                          true
% 2.75/0.98  --prep_upred                            true
% 2.75/0.98  --prep_sem_filter                       exhaustive
% 2.75/0.98  --prep_sem_filter_out                   false
% 2.75/0.98  --pred_elim                             true
% 2.75/0.98  --res_sim_input                         true
% 2.75/0.98  --eq_ax_congr_red                       true
% 2.75/0.98  --pure_diseq_elim                       true
% 2.75/0.98  --brand_transform                       false
% 2.75/0.98  --non_eq_to_eq                          false
% 2.75/0.98  --prep_def_merge                        true
% 2.75/0.98  --prep_def_merge_prop_impl              false
% 2.75/0.98  --prep_def_merge_mbd                    true
% 2.75/0.98  --prep_def_merge_tr_red                 false
% 2.75/0.98  --prep_def_merge_tr_cl                  false
% 2.75/0.98  --smt_preprocessing                     true
% 2.75/0.98  --smt_ac_axioms                         fast
% 2.75/0.98  --preprocessed_out                      false
% 2.75/0.98  --preprocessed_stats                    false
% 2.75/0.98  
% 2.75/0.98  ------ Abstraction refinement Options
% 2.75/0.98  
% 2.75/0.98  --abstr_ref                             []
% 2.75/0.98  --abstr_ref_prep                        false
% 2.75/0.98  --abstr_ref_until_sat                   false
% 2.75/0.98  --abstr_ref_sig_restrict                funpre
% 2.75/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.75/0.98  --abstr_ref_under                       []
% 2.75/0.98  
% 2.75/0.98  ------ SAT Options
% 2.75/0.98  
% 2.75/0.98  --sat_mode                              false
% 2.75/0.98  --sat_fm_restart_options                ""
% 2.75/0.98  --sat_gr_def                            false
% 2.75/0.98  --sat_epr_types                         true
% 2.75/0.98  --sat_non_cyclic_types                  false
% 2.75/0.98  --sat_finite_models                     false
% 2.75/0.98  --sat_fm_lemmas                         false
% 2.75/0.98  --sat_fm_prep                           false
% 2.75/0.98  --sat_fm_uc_incr                        true
% 2.75/0.98  --sat_out_model                         small
% 2.75/0.98  --sat_out_clauses                       false
% 2.75/0.98  
% 2.75/0.98  ------ QBF Options
% 2.75/0.98  
% 2.75/0.98  --qbf_mode                              false
% 2.75/0.98  --qbf_elim_univ                         false
% 2.75/0.98  --qbf_dom_inst                          none
% 2.75/0.98  --qbf_dom_pre_inst                      false
% 2.75/0.98  --qbf_sk_in                             false
% 2.75/0.98  --qbf_pred_elim                         true
% 2.75/0.98  --qbf_split                             512
% 2.75/0.98  
% 2.75/0.98  ------ BMC1 Options
% 2.75/0.98  
% 2.75/0.98  --bmc1_incremental                      false
% 2.75/0.98  --bmc1_axioms                           reachable_all
% 2.75/0.98  --bmc1_min_bound                        0
% 2.75/0.98  --bmc1_max_bound                        -1
% 2.75/0.98  --bmc1_max_bound_default                -1
% 2.75/0.98  --bmc1_symbol_reachability              true
% 2.75/0.98  --bmc1_property_lemmas                  false
% 2.75/0.98  --bmc1_k_induction                      false
% 2.75/0.98  --bmc1_non_equiv_states                 false
% 2.75/0.98  --bmc1_deadlock                         false
% 2.75/0.98  --bmc1_ucm                              false
% 2.75/0.98  --bmc1_add_unsat_core                   none
% 2.75/0.98  --bmc1_unsat_core_children              false
% 2.75/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.75/0.98  --bmc1_out_stat                         full
% 2.75/0.98  --bmc1_ground_init                      false
% 2.75/0.98  --bmc1_pre_inst_next_state              false
% 2.75/0.98  --bmc1_pre_inst_state                   false
% 2.75/0.98  --bmc1_pre_inst_reach_state             false
% 2.75/0.98  --bmc1_out_unsat_core                   false
% 2.75/0.98  --bmc1_aig_witness_out                  false
% 2.75/0.98  --bmc1_verbose                          false
% 2.75/0.98  --bmc1_dump_clauses_tptp                false
% 2.75/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.75/0.98  --bmc1_dump_file                        -
% 2.75/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.75/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.75/0.98  --bmc1_ucm_extend_mode                  1
% 2.75/0.98  --bmc1_ucm_init_mode                    2
% 2.75/0.98  --bmc1_ucm_cone_mode                    none
% 2.75/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.75/0.98  --bmc1_ucm_relax_model                  4
% 2.75/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.75/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.75/0.98  --bmc1_ucm_layered_model                none
% 2.75/0.98  --bmc1_ucm_max_lemma_size               10
% 2.75/0.98  
% 2.75/0.98  ------ AIG Options
% 2.75/0.98  
% 2.75/0.98  --aig_mode                              false
% 2.75/0.98  
% 2.75/0.98  ------ Instantiation Options
% 2.75/0.98  
% 2.75/0.98  --instantiation_flag                    true
% 2.75/0.98  --inst_sos_flag                         false
% 2.75/0.98  --inst_sos_phase                        true
% 2.75/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.75/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.75/0.98  --inst_lit_sel_side                     num_symb
% 2.75/0.98  --inst_solver_per_active                1400
% 2.75/0.98  --inst_solver_calls_frac                1.
% 2.75/0.98  --inst_passive_queue_type               priority_queues
% 2.75/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.75/0.98  --inst_passive_queues_freq              [25;2]
% 2.75/0.98  --inst_dismatching                      true
% 2.75/0.98  --inst_eager_unprocessed_to_passive     true
% 2.75/0.98  --inst_prop_sim_given                   true
% 2.75/0.98  --inst_prop_sim_new                     false
% 2.75/0.98  --inst_subs_new                         false
% 2.75/0.98  --inst_eq_res_simp                      false
% 2.75/0.98  --inst_subs_given                       false
% 2.75/0.98  --inst_orphan_elimination               true
% 2.75/0.98  --inst_learning_loop_flag               true
% 2.75/0.98  --inst_learning_start                   3000
% 2.75/0.98  --inst_learning_factor                  2
% 2.75/0.98  --inst_start_prop_sim_after_learn       3
% 2.75/0.98  --inst_sel_renew                        solver
% 2.75/0.98  --inst_lit_activity_flag                true
% 2.75/0.98  --inst_restr_to_given                   false
% 2.75/0.98  --inst_activity_threshold               500
% 2.75/0.98  --inst_out_proof                        true
% 2.75/0.98  
% 2.75/0.98  ------ Resolution Options
% 2.75/0.98  
% 2.75/0.98  --resolution_flag                       true
% 2.75/0.98  --res_lit_sel                           adaptive
% 2.75/0.98  --res_lit_sel_side                      none
% 2.75/0.98  --res_ordering                          kbo
% 2.75/0.98  --res_to_prop_solver                    active
% 2.75/0.98  --res_prop_simpl_new                    false
% 2.75/0.98  --res_prop_simpl_given                  true
% 2.75/0.98  --res_passive_queue_type                priority_queues
% 2.75/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.75/0.98  --res_passive_queues_freq               [15;5]
% 2.75/0.98  --res_forward_subs                      full
% 2.75/0.98  --res_backward_subs                     full
% 2.75/0.98  --res_forward_subs_resolution           true
% 2.75/0.98  --res_backward_subs_resolution          true
% 2.75/0.98  --res_orphan_elimination                true
% 2.75/0.98  --res_time_limit                        2.
% 2.75/0.98  --res_out_proof                         true
% 2.75/0.98  
% 2.75/0.98  ------ Superposition Options
% 2.75/0.98  
% 2.75/0.98  --superposition_flag                    true
% 2.75/0.98  --sup_passive_queue_type                priority_queues
% 2.75/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.75/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.75/0.98  --demod_completeness_check              fast
% 2.75/0.98  --demod_use_ground                      true
% 2.75/0.98  --sup_to_prop_solver                    passive
% 2.75/0.98  --sup_prop_simpl_new                    true
% 2.75/0.98  --sup_prop_simpl_given                  true
% 2.75/0.98  --sup_fun_splitting                     false
% 2.75/0.98  --sup_smt_interval                      50000
% 2.75/0.98  
% 2.75/0.98  ------ Superposition Simplification Setup
% 2.75/0.98  
% 2.75/0.98  --sup_indices_passive                   []
% 2.75/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.75/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/0.98  --sup_full_bw                           [BwDemod]
% 2.75/0.98  --sup_immed_triv                        [TrivRules]
% 2.75/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.75/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/0.98  --sup_immed_bw_main                     []
% 2.75/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.75/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/0.98  
% 2.75/0.98  ------ Combination Options
% 2.75/0.98  
% 2.75/0.98  --comb_res_mult                         3
% 2.75/0.98  --comb_sup_mult                         2
% 2.75/0.98  --comb_inst_mult                        10
% 2.75/0.98  
% 2.75/0.98  ------ Debug Options
% 2.75/0.98  
% 2.75/0.98  --dbg_backtrace                         false
% 2.75/0.98  --dbg_dump_prop_clauses                 false
% 2.75/0.98  --dbg_dump_prop_clauses_file            -
% 2.75/0.98  --dbg_out_stat                          false
% 2.75/0.98  ------ Parsing...
% 2.75/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.75/0.98  
% 2.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.75/0.98  
% 2.75/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.75/0.98  
% 2.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.75/0.98  ------ Proving...
% 2.75/0.98  ------ Problem Properties 
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  clauses                                 29
% 2.75/0.98  conjectures                             6
% 2.75/0.98  EPR                                     8
% 2.75/0.98  Horn                                    22
% 2.75/0.98  unary                                   10
% 2.75/0.98  binary                                  6
% 2.75/0.98  lits                                    73
% 2.75/0.98  lits eq                                 38
% 2.75/0.98  fd_pure                                 0
% 2.75/0.98  fd_pseudo                               0
% 2.75/0.98  fd_cond                                 8
% 2.75/0.98  fd_pseudo_cond                          1
% 2.75/0.98  AC symbols                              0
% 2.75/0.98  
% 2.75/0.98  ------ Schedule dynamic 5 is on 
% 2.75/0.98  
% 2.75/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  ------ 
% 2.75/0.98  Current options:
% 2.75/0.98  ------ 
% 2.75/0.98  
% 2.75/0.98  ------ Input Options
% 2.75/0.98  
% 2.75/0.98  --out_options                           all
% 2.75/0.98  --tptp_safe_out                         true
% 2.75/0.98  --problem_path                          ""
% 2.75/0.98  --include_path                          ""
% 2.75/0.98  --clausifier                            res/vclausify_rel
% 2.75/0.98  --clausifier_options                    --mode clausify
% 2.75/0.98  --stdin                                 false
% 2.75/0.98  --stats_out                             all
% 2.75/0.98  
% 2.75/0.98  ------ General Options
% 2.75/0.98  
% 2.75/0.98  --fof                                   false
% 2.75/0.98  --time_out_real                         305.
% 2.75/0.98  --time_out_virtual                      -1.
% 2.75/0.98  --symbol_type_check                     false
% 2.75/0.98  --clausify_out                          false
% 2.75/0.98  --sig_cnt_out                           false
% 2.75/0.98  --trig_cnt_out                          false
% 2.75/0.98  --trig_cnt_out_tolerance                1.
% 2.75/0.98  --trig_cnt_out_sk_spl                   false
% 2.75/0.98  --abstr_cl_out                          false
% 2.75/0.98  
% 2.75/0.98  ------ Global Options
% 2.75/0.98  
% 2.75/0.98  --schedule                              default
% 2.75/0.98  --add_important_lit                     false
% 2.75/0.98  --prop_solver_per_cl                    1000
% 2.75/0.98  --min_unsat_core                        false
% 2.75/0.98  --soft_assumptions                      false
% 2.75/0.98  --soft_lemma_size                       3
% 2.75/0.98  --prop_impl_unit_size                   0
% 2.75/0.98  --prop_impl_unit                        []
% 2.75/0.98  --share_sel_clauses                     true
% 2.75/0.98  --reset_solvers                         false
% 2.75/0.98  --bc_imp_inh                            [conj_cone]
% 2.75/0.98  --conj_cone_tolerance                   3.
% 2.75/0.98  --extra_neg_conj                        none
% 2.75/0.98  --large_theory_mode                     true
% 2.75/0.98  --prolific_symb_bound                   200
% 2.75/0.98  --lt_threshold                          2000
% 2.75/0.98  --clause_weak_htbl                      true
% 2.75/0.98  --gc_record_bc_elim                     false
% 2.75/0.98  
% 2.75/0.98  ------ Preprocessing Options
% 2.75/0.98  
% 2.75/0.98  --preprocessing_flag                    true
% 2.75/0.98  --time_out_prep_mult                    0.1
% 2.75/0.98  --splitting_mode                        input
% 2.75/0.98  --splitting_grd                         true
% 2.75/0.98  --splitting_cvd                         false
% 2.75/0.98  --splitting_cvd_svl                     false
% 2.75/0.98  --splitting_nvd                         32
% 2.75/0.98  --sub_typing                            true
% 2.75/0.98  --prep_gs_sim                           true
% 2.75/0.98  --prep_unflatten                        true
% 2.75/0.98  --prep_res_sim                          true
% 2.75/0.98  --prep_upred                            true
% 2.75/0.98  --prep_sem_filter                       exhaustive
% 2.75/0.98  --prep_sem_filter_out                   false
% 2.75/0.98  --pred_elim                             true
% 2.75/0.98  --res_sim_input                         true
% 2.75/0.98  --eq_ax_congr_red                       true
% 2.75/0.98  --pure_diseq_elim                       true
% 2.75/0.98  --brand_transform                       false
% 2.75/0.98  --non_eq_to_eq                          false
% 2.75/0.98  --prep_def_merge                        true
% 2.75/0.98  --prep_def_merge_prop_impl              false
% 2.75/0.98  --prep_def_merge_mbd                    true
% 2.75/0.98  --prep_def_merge_tr_red                 false
% 2.75/0.98  --prep_def_merge_tr_cl                  false
% 2.75/0.98  --smt_preprocessing                     true
% 2.75/0.98  --smt_ac_axioms                         fast
% 2.75/0.98  --preprocessed_out                      false
% 2.75/0.98  --preprocessed_stats                    false
% 2.75/0.98  
% 2.75/0.98  ------ Abstraction refinement Options
% 2.75/0.98  
% 2.75/0.98  --abstr_ref                             []
% 2.75/0.98  --abstr_ref_prep                        false
% 2.75/0.98  --abstr_ref_until_sat                   false
% 2.75/0.98  --abstr_ref_sig_restrict                funpre
% 2.75/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.75/0.98  --abstr_ref_under                       []
% 2.75/0.98  
% 2.75/0.98  ------ SAT Options
% 2.75/0.98  
% 2.75/0.98  --sat_mode                              false
% 2.75/0.98  --sat_fm_restart_options                ""
% 2.75/0.98  --sat_gr_def                            false
% 2.75/0.98  --sat_epr_types                         true
% 2.75/0.98  --sat_non_cyclic_types                  false
% 2.75/0.98  --sat_finite_models                     false
% 2.75/0.98  --sat_fm_lemmas                         false
% 2.75/0.98  --sat_fm_prep                           false
% 2.75/0.98  --sat_fm_uc_incr                        true
% 2.75/0.98  --sat_out_model                         small
% 2.75/0.98  --sat_out_clauses                       false
% 2.75/0.98  
% 2.75/0.98  ------ QBF Options
% 2.75/0.98  
% 2.75/0.98  --qbf_mode                              false
% 2.75/0.98  --qbf_elim_univ                         false
% 2.75/0.98  --qbf_dom_inst                          none
% 2.75/0.98  --qbf_dom_pre_inst                      false
% 2.75/0.98  --qbf_sk_in                             false
% 2.75/0.98  --qbf_pred_elim                         true
% 2.75/0.98  --qbf_split                             512
% 2.75/0.98  
% 2.75/0.98  ------ BMC1 Options
% 2.75/0.98  
% 2.75/0.98  --bmc1_incremental                      false
% 2.75/0.98  --bmc1_axioms                           reachable_all
% 2.75/0.98  --bmc1_min_bound                        0
% 2.75/0.98  --bmc1_max_bound                        -1
% 2.75/0.98  --bmc1_max_bound_default                -1
% 2.75/0.98  --bmc1_symbol_reachability              true
% 2.75/0.98  --bmc1_property_lemmas                  false
% 2.75/0.98  --bmc1_k_induction                      false
% 2.75/0.98  --bmc1_non_equiv_states                 false
% 2.75/0.98  --bmc1_deadlock                         false
% 2.75/0.98  --bmc1_ucm                              false
% 2.75/0.98  --bmc1_add_unsat_core                   none
% 2.75/0.98  --bmc1_unsat_core_children              false
% 2.75/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.75/0.98  --bmc1_out_stat                         full
% 2.75/0.98  --bmc1_ground_init                      false
% 2.75/0.98  --bmc1_pre_inst_next_state              false
% 2.75/0.98  --bmc1_pre_inst_state                   false
% 2.75/0.98  --bmc1_pre_inst_reach_state             false
% 2.75/0.98  --bmc1_out_unsat_core                   false
% 2.75/0.98  --bmc1_aig_witness_out                  false
% 2.75/0.98  --bmc1_verbose                          false
% 2.75/0.98  --bmc1_dump_clauses_tptp                false
% 2.75/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.75/0.98  --bmc1_dump_file                        -
% 2.75/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.75/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.75/0.98  --bmc1_ucm_extend_mode                  1
% 2.75/0.98  --bmc1_ucm_init_mode                    2
% 2.75/0.98  --bmc1_ucm_cone_mode                    none
% 2.75/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.75/0.98  --bmc1_ucm_relax_model                  4
% 2.75/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.75/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.75/0.98  --bmc1_ucm_layered_model                none
% 2.75/0.98  --bmc1_ucm_max_lemma_size               10
% 2.75/0.98  
% 2.75/0.98  ------ AIG Options
% 2.75/0.98  
% 2.75/0.98  --aig_mode                              false
% 2.75/0.98  
% 2.75/0.98  ------ Instantiation Options
% 2.75/0.98  
% 2.75/0.98  --instantiation_flag                    true
% 2.75/0.98  --inst_sos_flag                         false
% 2.75/0.98  --inst_sos_phase                        true
% 2.75/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.75/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.75/0.98  --inst_lit_sel_side                     none
% 2.75/0.98  --inst_solver_per_active                1400
% 2.75/0.98  --inst_solver_calls_frac                1.
% 2.75/0.98  --inst_passive_queue_type               priority_queues
% 2.75/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.75/0.98  --inst_passive_queues_freq              [25;2]
% 2.75/0.98  --inst_dismatching                      true
% 2.75/0.98  --inst_eager_unprocessed_to_passive     true
% 2.75/0.98  --inst_prop_sim_given                   true
% 2.75/0.98  --inst_prop_sim_new                     false
% 2.75/0.98  --inst_subs_new                         false
% 2.75/0.98  --inst_eq_res_simp                      false
% 2.75/0.98  --inst_subs_given                       false
% 2.75/0.98  --inst_orphan_elimination               true
% 2.75/0.98  --inst_learning_loop_flag               true
% 2.75/0.98  --inst_learning_start                   3000
% 2.75/0.98  --inst_learning_factor                  2
% 2.75/0.98  --inst_start_prop_sim_after_learn       3
% 2.75/0.98  --inst_sel_renew                        solver
% 2.75/0.98  --inst_lit_activity_flag                true
% 2.75/0.98  --inst_restr_to_given                   false
% 2.75/0.98  --inst_activity_threshold               500
% 2.75/0.98  --inst_out_proof                        true
% 2.75/0.98  
% 2.75/0.98  ------ Resolution Options
% 2.75/0.98  
% 2.75/0.98  --resolution_flag                       false
% 2.75/0.98  --res_lit_sel                           adaptive
% 2.75/0.98  --res_lit_sel_side                      none
% 2.75/0.98  --res_ordering                          kbo
% 2.75/0.98  --res_to_prop_solver                    active
% 2.75/0.98  --res_prop_simpl_new                    false
% 2.75/0.98  --res_prop_simpl_given                  true
% 2.75/0.98  --res_passive_queue_type                priority_queues
% 2.75/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.75/0.98  --res_passive_queues_freq               [15;5]
% 2.75/0.98  --res_forward_subs                      full
% 2.75/0.98  --res_backward_subs                     full
% 2.75/0.98  --res_forward_subs_resolution           true
% 2.75/0.98  --res_backward_subs_resolution          true
% 2.75/0.98  --res_orphan_elimination                true
% 2.75/0.98  --res_time_limit                        2.
% 2.75/0.98  --res_out_proof                         true
% 2.75/0.98  
% 2.75/0.98  ------ Superposition Options
% 2.75/0.98  
% 2.75/0.98  --superposition_flag                    true
% 2.75/0.98  --sup_passive_queue_type                priority_queues
% 2.75/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.75/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.75/0.98  --demod_completeness_check              fast
% 2.75/0.98  --demod_use_ground                      true
% 2.75/0.98  --sup_to_prop_solver                    passive
% 2.75/0.98  --sup_prop_simpl_new                    true
% 2.75/0.98  --sup_prop_simpl_given                  true
% 2.75/0.98  --sup_fun_splitting                     false
% 2.75/0.98  --sup_smt_interval                      50000
% 2.75/0.98  
% 2.75/0.98  ------ Superposition Simplification Setup
% 2.75/0.98  
% 2.75/0.98  --sup_indices_passive                   []
% 2.75/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.75/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/0.98  --sup_full_bw                           [BwDemod]
% 2.75/0.98  --sup_immed_triv                        [TrivRules]
% 2.75/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.75/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/0.98  --sup_immed_bw_main                     []
% 2.75/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.75/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/0.98  
% 2.75/0.98  ------ Combination Options
% 2.75/0.98  
% 2.75/0.98  --comb_res_mult                         3
% 2.75/0.98  --comb_sup_mult                         2
% 2.75/0.98  --comb_inst_mult                        10
% 2.75/0.98  
% 2.75/0.98  ------ Debug Options
% 2.75/0.98  
% 2.75/0.98  --dbg_backtrace                         false
% 2.75/0.98  --dbg_dump_prop_clauses                 false
% 2.75/0.98  --dbg_dump_prop_clauses_file            -
% 2.75/0.98  --dbg_out_stat                          false
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  ------ Proving...
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  % SZS status Theorem for theBenchmark.p
% 2.75/0.98  
% 2.75/0.98   Resolution empty clause
% 2.75/0.98  
% 2.75/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.75/0.98  
% 2.75/0.98  fof(f14,axiom,(
% 2.75/0.98    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 2.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.98  
% 2.75/0.98  fof(f36,plain,(
% 2.75/0.98    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.75/0.98    inference(nnf_transformation,[],[f14])).
% 2.75/0.98  
% 2.75/0.98  fof(f37,plain,(
% 2.75/0.98    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) & (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.75/0.98    inference(flattening,[],[f36])).
% 2.75/0.98  
% 2.75/0.98  fof(f63,plain,(
% 2.75/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 2.75/0.98    inference(cnf_transformation,[],[f37])).
% 2.75/0.98  
% 2.75/0.98  fof(f8,axiom,(
% 2.75/0.98    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 2.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.98  
% 2.75/0.98  fof(f51,plain,(
% 2.75/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.75/0.98    inference(cnf_transformation,[],[f8])).
% 2.75/0.98  
% 2.75/0.98  fof(f7,axiom,(
% 2.75/0.98    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 2.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.98  
% 2.75/0.98  fof(f50,plain,(
% 2.75/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 2.75/0.98    inference(cnf_transformation,[],[f7])).
% 2.75/0.98  
% 2.75/0.98  fof(f73,plain,(
% 2.75/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.75/0.98    inference(definition_unfolding,[],[f51,f50])).
% 2.75/0.98  
% 2.75/0.98  fof(f82,plain,(
% 2.75/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 2.75/0.98    inference(definition_unfolding,[],[f63,f73])).
% 2.75/0.98  
% 2.75/0.98  fof(f91,plain,(
% 2.75/0.98    ( ! [X2,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0) )),
% 2.75/0.98    inference(equality_resolution,[],[f82])).
% 2.75/0.98  
% 2.75/0.98  fof(f62,plain,(
% 2.75/0.98    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.75/0.98    inference(cnf_transformation,[],[f37])).
% 2.75/0.98  
% 2.75/0.98  fof(f83,plain,(
% 2.75/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.75/0.98    inference(definition_unfolding,[],[f62,f73])).
% 2.75/0.98  
% 2.75/0.98  fof(f15,conjecture,(
% 2.75/0.98    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.98  
% 2.75/0.98  fof(f16,negated_conjecture,(
% 2.75/0.98    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.75/0.98    inference(negated_conjecture,[],[f15])).
% 2.75/0.98  
% 2.75/0.98  fof(f28,plain,(
% 2.75/0.98    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.75/0.98    inference(ennf_transformation,[],[f16])).
% 2.75/0.98  
% 2.75/0.98  fof(f29,plain,(
% 2.75/0.98    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.75/0.98    inference(flattening,[],[f28])).
% 2.75/0.98  
% 2.75/0.98  fof(f38,plain,(
% 2.75/0.98    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 2.75/0.99    introduced(choice_axiom,[])).
% 2.75/0.99  
% 2.75/0.99  fof(f39,plain,(
% 2.75/0.99    k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 2.75/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f29,f38])).
% 2.75/0.99  
% 2.75/0.99  fof(f69,plain,(
% 2.75/0.99    k1_xboole_0 != sK3),
% 2.75/0.99    inference(cnf_transformation,[],[f39])).
% 2.75/0.99  
% 2.75/0.99  fof(f70,plain,(
% 2.75/0.99    k1_xboole_0 != sK4),
% 2.75/0.99    inference(cnf_transformation,[],[f39])).
% 2.75/0.99  
% 2.75/0.99  fof(f71,plain,(
% 2.75/0.99    k1_xboole_0 != sK5),
% 2.75/0.99    inference(cnf_transformation,[],[f39])).
% 2.75/0.99  
% 2.75/0.99  fof(f67,plain,(
% 2.75/0.99    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 2.75/0.99    inference(cnf_transformation,[],[f39])).
% 2.75/0.99  
% 2.75/0.99  fof(f85,plain,(
% 2.75/0.99    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.75/0.99    inference(definition_unfolding,[],[f67,f50])).
% 2.75/0.99  
% 2.75/0.99  fof(f5,axiom,(
% 2.75/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.99  
% 2.75/0.99  fof(f21,plain,(
% 2.75/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.75/0.99    inference(ennf_transformation,[],[f5])).
% 2.75/0.99  
% 2.75/0.99  fof(f22,plain,(
% 2.75/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.75/0.99    inference(flattening,[],[f21])).
% 2.75/0.99  
% 2.75/0.99  fof(f48,plain,(
% 2.75/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.75/0.99    inference(cnf_transformation,[],[f22])).
% 2.75/0.99  
% 2.75/0.99  fof(f10,axiom,(
% 2.75/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.99  
% 2.75/0.99  fof(f24,plain,(
% 2.75/0.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.75/0.99    inference(ennf_transformation,[],[f10])).
% 2.75/0.99  
% 2.75/0.99  fof(f53,plain,(
% 2.75/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.75/0.99    inference(cnf_transformation,[],[f24])).
% 2.75/0.99  
% 2.75/0.99  fof(f11,axiom,(
% 2.75/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.99  
% 2.75/0.99  fof(f25,plain,(
% 2.75/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.75/0.99    inference(ennf_transformation,[],[f11])).
% 2.75/0.99  
% 2.75/0.99  fof(f34,plain,(
% 2.75/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 2.75/0.99    introduced(choice_axiom,[])).
% 2.75/0.99  
% 2.75/0.99  fof(f35,plain,(
% 2.75/0.99    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 2.75/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f34])).
% 2.75/0.99  
% 2.75/0.99  fof(f55,plain,(
% 2.75/0.99    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.75/0.99    inference(cnf_transformation,[],[f35])).
% 2.75/0.99  
% 2.75/0.99  fof(f1,axiom,(
% 2.75/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.99  
% 2.75/0.99  fof(f17,plain,(
% 2.75/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.75/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.75/0.99  
% 2.75/0.99  fof(f18,plain,(
% 2.75/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.75/0.99    inference(ennf_transformation,[],[f17])).
% 2.75/0.99  
% 2.75/0.99  fof(f40,plain,(
% 2.75/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.75/0.99    inference(cnf_transformation,[],[f18])).
% 2.75/0.99  
% 2.75/0.99  fof(f4,axiom,(
% 2.75/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.99  
% 2.75/0.99  fof(f20,plain,(
% 2.75/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.75/0.99    inference(ennf_transformation,[],[f4])).
% 2.75/0.99  
% 2.75/0.99  fof(f47,plain,(
% 2.75/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.75/0.99    inference(cnf_transformation,[],[f20])).
% 2.75/0.99  
% 2.75/0.99  fof(f12,axiom,(
% 2.75/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.99  
% 2.75/0.99  fof(f26,plain,(
% 2.75/0.99    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.75/0.99    inference(ennf_transformation,[],[f12])).
% 2.75/0.99  
% 2.75/0.99  fof(f58,plain,(
% 2.75/0.99    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.75/0.99    inference(cnf_transformation,[],[f26])).
% 2.75/0.99  
% 2.75/0.99  fof(f6,axiom,(
% 2.75/0.99    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 2.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.99  
% 2.75/0.99  fof(f49,plain,(
% 2.75/0.99    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 2.75/0.99    inference(cnf_transformation,[],[f6])).
% 2.75/0.99  
% 2.75/0.99  fof(f75,plain,(
% 2.75/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.75/0.99    inference(definition_unfolding,[],[f58,f49,f50])).
% 2.75/0.99  
% 2.75/0.99  fof(f13,axiom,(
% 2.75/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.99  
% 2.75/0.99  fof(f27,plain,(
% 2.75/0.99    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.75/0.99    inference(ennf_transformation,[],[f13])).
% 2.75/0.99  
% 2.75/0.99  fof(f59,plain,(
% 2.75/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.75/0.99    inference(cnf_transformation,[],[f27])).
% 2.75/0.99  
% 2.75/0.99  fof(f78,plain,(
% 2.75/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.75/0.99    inference(definition_unfolding,[],[f59,f50])).
% 2.75/0.99  
% 2.75/0.99  fof(f60,plain,(
% 2.75/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.75/0.99    inference(cnf_transformation,[],[f27])).
% 2.75/0.99  
% 2.75/0.99  fof(f77,plain,(
% 2.75/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.75/0.99    inference(definition_unfolding,[],[f60,f50])).
% 2.75/0.99  
% 2.75/0.99  fof(f61,plain,(
% 2.75/0.99    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.75/0.99    inference(cnf_transformation,[],[f27])).
% 2.75/0.99  
% 2.75/0.99  fof(f76,plain,(
% 2.75/0.99    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.75/0.99    inference(definition_unfolding,[],[f61,f50])).
% 2.75/0.99  
% 2.75/0.99  fof(f68,plain,(
% 2.75/0.99    ( ! [X6,X7,X5] : (sK6 = X7 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 2.75/0.99    inference(cnf_transformation,[],[f39])).
% 2.75/0.99  
% 2.75/0.99  fof(f84,plain,(
% 2.75/0.99    ( ! [X6,X7,X5] : (sK6 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 2.75/0.99    inference(definition_unfolding,[],[f68,f49])).
% 2.75/0.99  
% 2.75/0.99  fof(f72,plain,(
% 2.75/0.99    k7_mcart_1(sK3,sK4,sK5,sK7) != sK6),
% 2.75/0.99    inference(cnf_transformation,[],[f39])).
% 2.75/0.99  
% 2.75/0.99  fof(f9,axiom,(
% 2.75/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 2.75/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.75/0.99  
% 2.75/0.99  fof(f23,plain,(
% 2.75/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 2.75/0.99    inference(ennf_transformation,[],[f9])).
% 2.75/0.99  
% 2.75/0.99  fof(f52,plain,(
% 2.75/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 2.75/0.99    inference(cnf_transformation,[],[f23])).
% 2.75/0.99  
% 2.75/0.99  fof(f74,plain,(
% 2.75/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 2.75/0.99    inference(definition_unfolding,[],[f52,f50])).
% 2.75/0.99  
% 2.75/0.99  fof(f54,plain,(
% 2.75/0.99    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.75/0.99    inference(cnf_transformation,[],[f24])).
% 2.75/0.99  
% 2.75/0.99  fof(f65,plain,(
% 2.75/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0) )),
% 2.75/0.99    inference(cnf_transformation,[],[f37])).
% 2.75/0.99  
% 2.75/0.99  fof(f80,plain,(
% 2.75/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 2.75/0.99    inference(definition_unfolding,[],[f65,f73])).
% 2.75/0.99  
% 2.75/0.99  fof(f89,plain,(
% 2.75/0.99    ( ! [X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) = k1_xboole_0) )),
% 2.75/0.99    inference(equality_resolution,[],[f80])).
% 2.75/0.99  
% 2.75/0.99  cnf(c_22,plain,
% 2.75/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 2.75/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_23,plain,
% 2.75/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 2.75/0.99      | k1_xboole_0 = X0
% 2.75/0.99      | k1_xboole_0 = X1
% 2.75/0.99      | k1_xboole_0 = X2
% 2.75/0.99      | k1_xboole_0 = X3 ),
% 2.75/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_1519,plain,
% 2.75/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 2.75/0.99      | k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0
% 2.75/0.99      | k1_xboole_0 = X0
% 2.75/0.99      | k1_xboole_0 = X2
% 2.75/0.99      | k1_xboole_0 = X3 ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_22,c_23]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_27,negated_conjecture,
% 2.75/0.99      ( k1_xboole_0 != sK3 ),
% 2.75/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_26,negated_conjecture,
% 2.75/0.99      ( k1_xboole_0 != sK4 ),
% 2.75/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_25,negated_conjecture,
% 2.75/0.99      ( k1_xboole_0 != sK5 ),
% 2.75/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_34,plain,
% 2.75/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 2.75/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.75/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_35,plain,
% 2.75/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 2.75/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_418,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_1005,plain,
% 2.75/0.99      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.75/0.99      inference(instantiation,[status(thm)],[c_418]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_1006,plain,
% 2.75/0.99      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 2.75/0.99      inference(instantiation,[status(thm)],[c_1005]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_1007,plain,
% 2.75/0.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.75/0.99      inference(instantiation,[status(thm)],[c_418]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_1008,plain,
% 2.75/0.99      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 2.75/0.99      inference(instantiation,[status(thm)],[c_1007]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_1009,plain,
% 2.75/0.99      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.75/0.99      inference(instantiation,[status(thm)],[c_418]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_1010,plain,
% 2.75/0.99      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.75/0.99      inference(instantiation,[status(thm)],[c_1009]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_29,negated_conjecture,
% 2.75/0.99      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 2.75/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_768,plain,
% 2.75/0.99      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_8,plain,
% 2.75/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.75/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_780,plain,
% 2.75/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.75/0.99      | r2_hidden(X0,X1) = iProver_top
% 2.75/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_2498,plain,
% 2.75/0.99      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top
% 2.75/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_768,c_780]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_11,plain,
% 2.75/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.75/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_777,plain,
% 2.75/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.75/0.99      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_2630,plain,
% 2.75/0.99      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) = iProver_top
% 2.75/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_2498,c_777]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3115,plain,
% 2.75/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top
% 2.75/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_2630,c_777]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_14,plain,
% 2.75/0.99      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.75/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_774,plain,
% 2.75/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_0,plain,
% 2.75/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.75/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_787,plain,
% 2.75/0.99      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_2248,plain,
% 2.75/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_774,c_787]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3662,plain,
% 2.75/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 2.75/0.99      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_3115,c_2248]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3730,plain,
% 2.75/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 2.75/0.99      | v1_xboole_0(sK3) != iProver_top ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_3662,c_787]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_7,plain,
% 2.75/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.75/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_781,plain,
% 2.75/0.99      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3731,plain,
% 2.75/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 2.75/0.99      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) = iProver_top ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_3662,c_781]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_15,plain,
% 2.75/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.75/0.99      | k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0)),k7_mcart_1(X1,X2,X3,X0)) = X0
% 2.75/0.99      | k1_xboole_0 = X1
% 2.75/0.99      | k1_xboole_0 = X2
% 2.75/0.99      | k1_xboole_0 = X3 ),
% 2.75/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_773,plain,
% 2.75/0.99      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
% 2.75/0.99      | k1_xboole_0 = X0
% 2.75/0.99      | k1_xboole_0 = X1
% 2.75/0.99      | k1_xboole_0 = X2
% 2.75/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3748,plain,
% 2.75/0.99      ( k4_tarski(k4_tarski(k5_mcart_1(sK3,sK4,sK5,sK7),k6_mcart_1(sK3,sK4,sK5,sK7)),k7_mcart_1(sK3,sK4,sK5,sK7)) = sK7
% 2.75/0.99      | sK5 = k1_xboole_0
% 2.75/0.99      | sK4 = k1_xboole_0
% 2.75/0.99      | sK3 = k1_xboole_0 ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_768,c_773]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_18,plain,
% 2.75/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.75/0.99      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.75/0.99      | k1_xboole_0 = X1
% 2.75/0.99      | k1_xboole_0 = X2
% 2.75/0.99      | k1_xboole_0 = X3 ),
% 2.75/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_770,plain,
% 2.75/0.99      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.75/0.99      | k1_xboole_0 = X0
% 2.75/0.99      | k1_xboole_0 = X1
% 2.75/0.99      | k1_xboole_0 = X2
% 2.75/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_1242,plain,
% 2.75/0.99      ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 2.75/0.99      | sK5 = k1_xboole_0
% 2.75/0.99      | sK4 = k1_xboole_0
% 2.75/0.99      | sK3 = k1_xboole_0 ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_768,c_770]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_1574,plain,
% 2.75/0.99      ( k5_mcart_1(sK3,sK4,sK5,sK7) = k1_mcart_1(k1_mcart_1(sK7)) ),
% 2.75/0.99      inference(global_propositional_subsumption,
% 2.75/0.99                [status(thm)],
% 2.75/0.99                [c_1242,c_27,c_26,c_25,c_34,c_35,c_1006,c_1008,c_1010]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_17,plain,
% 2.75/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.75/0.99      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.75/0.99      | k1_xboole_0 = X1
% 2.75/0.99      | k1_xboole_0 = X2
% 2.75/0.99      | k1_xboole_0 = X3 ),
% 2.75/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_771,plain,
% 2.75/0.99      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.75/0.99      | k1_xboole_0 = X0
% 2.75/0.99      | k1_xboole_0 = X1
% 2.75/0.99      | k1_xboole_0 = X2
% 2.75/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_2041,plain,
% 2.75/0.99      ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 2.75/0.99      | sK5 = k1_xboole_0
% 2.75/0.99      | sK4 = k1_xboole_0
% 2.75/0.99      | sK3 = k1_xboole_0 ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_768,c_771]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_2641,plain,
% 2.75/0.99      ( k6_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(k1_mcart_1(sK7)) ),
% 2.75/0.99      inference(global_propositional_subsumption,
% 2.75/0.99                [status(thm)],
% 2.75/0.99                [c_2041,c_27,c_26,c_25,c_34,c_35,c_1006,c_1008,c_1010]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_16,plain,
% 2.75/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.75/0.99      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 2.75/0.99      | k1_xboole_0 = X1
% 2.75/0.99      | k1_xboole_0 = X2
% 2.75/0.99      | k1_xboole_0 = X3 ),
% 2.75/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_772,plain,
% 2.75/0.99      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 2.75/0.99      | k1_xboole_0 = X0
% 2.75/0.99      | k1_xboole_0 = X1
% 2.75/0.99      | k1_xboole_0 = X2
% 2.75/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3510,plain,
% 2.75/0.99      ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7)
% 2.75/0.99      | sK5 = k1_xboole_0
% 2.75/0.99      | sK4 = k1_xboole_0
% 2.75/0.99      | sK3 = k1_xboole_0 ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_768,c_772]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3654,plain,
% 2.75/0.99      ( k7_mcart_1(sK3,sK4,sK5,sK7) = k2_mcart_1(sK7) ),
% 2.75/0.99      inference(global_propositional_subsumption,
% 2.75/0.99                [status(thm)],
% 2.75/0.99                [c_3510,c_27,c_26,c_25,c_34,c_35,c_1006,c_1008,c_1010]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3793,plain,
% 2.75/0.99      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))),k2_mcart_1(sK7)) = sK7
% 2.75/0.99      | sK5 = k1_xboole_0
% 2.75/0.99      | sK4 = k1_xboole_0
% 2.75/0.99      | sK3 = k1_xboole_0 ),
% 2.75/0.99      inference(light_normalisation,
% 2.75/0.99                [status(thm)],
% 2.75/0.99                [c_3748,c_1574,c_2641,c_3654]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3990,plain,
% 2.75/0.99      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK7)),k2_mcart_1(k1_mcart_1(sK7))),k2_mcart_1(sK7)) = sK7 ),
% 2.75/0.99      inference(global_propositional_subsumption,
% 2.75/0.99                [status(thm)],
% 2.75/0.99                [c_3793,c_27,c_26,c_25,c_34,c_35,c_1006,c_1008,c_1010]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_28,negated_conjecture,
% 2.75/0.99      ( ~ m1_subset_1(X0,sK5)
% 2.75/0.99      | ~ m1_subset_1(X1,sK4)
% 2.75/0.99      | ~ m1_subset_1(X2,sK3)
% 2.75/0.99      | k4_tarski(k4_tarski(X2,X1),X0) != sK7
% 2.75/0.99      | sK6 = X0 ),
% 2.75/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_769,plain,
% 2.75/0.99      ( k4_tarski(k4_tarski(X0,X1),X2) != sK7
% 2.75/0.99      | sK6 = X2
% 2.75/0.99      | m1_subset_1(X2,sK5) != iProver_top
% 2.75/0.99      | m1_subset_1(X1,sK4) != iProver_top
% 2.75/0.99      | m1_subset_1(X0,sK3) != iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3994,plain,
% 2.75/0.99      ( k2_mcart_1(sK7) = sK6
% 2.75/0.99      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) != iProver_top
% 2.75/0.99      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
% 2.75/0.99      | m1_subset_1(k2_mcart_1(sK7),sK5) != iProver_top ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_3990,c_769]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_24,negated_conjecture,
% 2.75/0.99      ( k7_mcart_1(sK3,sK4,sK5,sK7) != sK6 ),
% 2.75/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3657,plain,
% 2.75/0.99      ( k2_mcart_1(sK7) != sK6 ),
% 2.75/0.99      inference(demodulation,[status(thm)],[c_3654,c_24]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_9,plain,
% 2.75/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.75/0.99      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
% 2.75/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_779,plain,
% 2.75/0.99      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 2.75/0.99      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3803,plain,
% 2.75/0.99      ( m1_subset_1(k7_mcart_1(sK3,sK4,sK5,sK7),sK5) = iProver_top ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_768,c_779]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3850,plain,
% 2.75/0.99      ( m1_subset_1(k2_mcart_1(sK7),sK5) = iProver_top ),
% 2.75/0.99      inference(light_normalisation,[status(thm)],[c_3803,c_3654]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_4043,plain,
% 2.75/0.99      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
% 2.75/0.99      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) != iProver_top ),
% 2.75/0.99      inference(global_propositional_subsumption,
% 2.75/0.99                [status(thm)],
% 2.75/0.99                [c_3994,c_3657,c_3850]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_4044,plain,
% 2.75/0.99      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK7)),sK3) != iProver_top
% 2.75/0.99      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
% 2.75/0.99      inference(renaming,[status(thm)],[c_4043]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_10,plain,
% 2.75/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.75/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_778,plain,
% 2.75/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.75/0.99      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 2.75/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3114,plain,
% 2.75/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
% 2.75/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_2630,c_778]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_3663,plain,
% 2.75/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 2.75/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_3114,c_2248]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_4067,plain,
% 2.75/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0
% 2.75/0.99      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_3663,c_781]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_4291,plain,
% 2.75/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) = k1_xboole_0 ),
% 2.75/0.99      inference(global_propositional_subsumption,
% 2.75/0.99                [status(thm)],
% 2.75/0.99                [c_3730,c_3731,c_4044,c_4067]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_4358,plain,
% 2.75/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 2.75/0.99      | sK5 = k1_xboole_0
% 2.75/0.99      | sK4 = k1_xboole_0
% 2.75/0.99      | sK3 = k1_xboole_0
% 2.75/0.99      | k1_xboole_0 = X0 ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_4291,c_23]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_20,plain,
% 2.75/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
% 2.75/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_1263,plain,
% 2.75/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.75/0.99      inference(superposition,[status(thm)],[c_20,c_20]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_4376,plain,
% 2.75/0.99      ( sK5 = k1_xboole_0
% 2.75/0.99      | sK4 = k1_xboole_0
% 2.75/0.99      | sK3 = k1_xboole_0
% 2.75/0.99      | k1_xboole_0 = X0
% 2.75/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.75/0.99      inference(light_normalisation,[status(thm)],[c_4358,c_1263]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_4377,plain,
% 2.75/0.99      ( sK5 = k1_xboole_0
% 2.75/0.99      | sK4 = k1_xboole_0
% 2.75/0.99      | sK3 = k1_xboole_0
% 2.75/0.99      | k1_xboole_0 = X0 ),
% 2.75/0.99      inference(equality_resolution_simp,[status(thm)],[c_4376]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_5274,plain,
% 2.75/0.99      ( k1_xboole_0 = X0 ),
% 2.75/0.99      inference(global_propositional_subsumption,
% 2.75/0.99                [status(thm)],
% 2.75/0.99                [c_1519,c_27,c_26,c_25,c_34,c_35,c_1006,c_1008,c_1010,c_4377]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_5306,plain,
% 2.75/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 2.75/0.99      inference(demodulation,[status(thm)],[c_5274,c_25]) ).
% 2.75/0.99  
% 2.75/0.99  cnf(c_5323,plain,
% 2.75/0.99      ( $false ),
% 2.75/0.99      inference(equality_resolution_simp,[status(thm)],[c_5306]) ).
% 2.75/0.99  
% 2.75/0.99  
% 2.75/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.75/0.99  
% 2.75/0.99  ------                               Statistics
% 2.75/0.99  
% 2.75/0.99  ------ General
% 2.75/0.99  
% 2.75/0.99  abstr_ref_over_cycles:                  0
% 2.75/0.99  abstr_ref_under_cycles:                 0
% 2.75/0.99  gc_basic_clause_elim:                   0
% 2.75/0.99  forced_gc_time:                         0
% 2.75/0.99  parsing_time:                           0.011
% 2.75/0.99  unif_index_cands_time:                  0.
% 2.75/0.99  unif_index_add_time:                    0.
% 2.75/0.99  orderings_time:                         0.
% 2.75/0.99  out_proof_time:                         0.009
% 2.75/0.99  total_time:                             0.177
% 2.75/0.99  num_of_symbols:                         52
% 2.75/0.99  num_of_terms:                           6151
% 2.75/0.99  
% 2.75/0.99  ------ Preprocessing
% 2.75/0.99  
% 2.75/0.99  num_of_splits:                          0
% 2.75/0.99  num_of_split_atoms:                     0
% 2.75/0.99  num_of_reused_defs:                     0
% 2.75/0.99  num_eq_ax_congr_red:                    63
% 2.75/0.99  num_of_sem_filtered_clauses:            1
% 2.75/0.99  num_of_subtypes:                        0
% 2.75/0.99  monotx_restored_types:                  0
% 2.75/0.99  sat_num_of_epr_types:                   0
% 2.75/0.99  sat_num_of_non_cyclic_types:            0
% 2.75/0.99  sat_guarded_non_collapsed_types:        0
% 2.75/0.99  num_pure_diseq_elim:                    0
% 2.75/0.99  simp_replaced_by:                       0
% 2.75/0.99  res_preprocessed:                       137
% 2.75/0.99  prep_upred:                             0
% 2.75/0.99  prep_unflattend:                        0
% 2.75/0.99  smt_new_axioms:                         0
% 2.75/0.99  pred_elim_cands:                        4
% 2.75/0.99  pred_elim:                              0
% 2.75/0.99  pred_elim_cl:                           0
% 2.75/0.99  pred_elim_cycles:                       2
% 2.75/0.99  merged_defs:                            0
% 2.75/0.99  merged_defs_ncl:                        0
% 2.75/0.99  bin_hyper_res:                          0
% 2.75/0.99  prep_cycles:                            4
% 2.75/0.99  pred_elim_time:                         0.002
% 2.75/0.99  splitting_time:                         0.
% 2.75/0.99  sem_filter_time:                        0.
% 2.75/0.99  monotx_time:                            0.
% 2.75/0.99  subtype_inf_time:                       0.
% 2.75/0.99  
% 2.75/0.99  ------ Problem properties
% 2.75/0.99  
% 2.75/0.99  clauses:                                29
% 2.75/0.99  conjectures:                            6
% 2.75/0.99  epr:                                    8
% 2.75/0.99  horn:                                   22
% 2.75/0.99  ground:                                 5
% 2.75/0.99  unary:                                  10
% 2.75/0.99  binary:                                 6
% 2.75/0.99  lits:                                   73
% 2.75/0.99  lits_eq:                                38
% 2.75/0.99  fd_pure:                                0
% 2.75/0.99  fd_pseudo:                              0
% 2.75/0.99  fd_cond:                                8
% 2.75/0.99  fd_pseudo_cond:                         1
% 2.75/0.99  ac_symbols:                             0
% 2.75/0.99  
% 2.75/0.99  ------ Propositional Solver
% 2.75/0.99  
% 2.75/0.99  prop_solver_calls:                      25
% 2.75/0.99  prop_fast_solver_calls:                 881
% 2.75/0.99  smt_solver_calls:                       0
% 2.75/0.99  smt_fast_solver_calls:                  0
% 2.75/0.99  prop_num_of_clauses:                    1867
% 2.75/0.99  prop_preprocess_simplified:             6616
% 2.75/0.99  prop_fo_subsumed:                       19
% 2.75/0.99  prop_solver_time:                       0.
% 2.75/0.99  smt_solver_time:                        0.
% 2.75/0.99  smt_fast_solver_time:                   0.
% 2.75/0.99  prop_fast_solver_time:                  0.
% 2.75/0.99  prop_unsat_core_time:                   0.
% 2.75/0.99  
% 2.75/0.99  ------ QBF
% 2.75/0.99  
% 2.75/0.99  qbf_q_res:                              0
% 2.75/0.99  qbf_num_tautologies:                    0
% 2.75/0.99  qbf_prep_cycles:                        0
% 2.75/0.99  
% 2.75/0.99  ------ BMC1
% 2.75/0.99  
% 2.75/0.99  bmc1_current_bound:                     -1
% 2.75/0.99  bmc1_last_solved_bound:                 -1
% 2.75/0.99  bmc1_unsat_core_size:                   -1
% 2.75/0.99  bmc1_unsat_core_parents_size:           -1
% 2.75/0.99  bmc1_merge_next_fun:                    0
% 2.75/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.75/0.99  
% 2.75/0.99  ------ Instantiation
% 2.75/0.99  
% 2.75/0.99  inst_num_of_clauses:                    631
% 2.75/0.99  inst_num_in_passive:                    72
% 2.75/0.99  inst_num_in_active:                     316
% 2.75/0.99  inst_num_in_unprocessed:                243
% 2.75/0.99  inst_num_of_loops:                      320
% 2.75/0.99  inst_num_of_learning_restarts:          0
% 2.75/0.99  inst_num_moves_active_passive:          3
% 2.75/0.99  inst_lit_activity:                      0
% 2.75/0.99  inst_lit_activity_moves:                0
% 2.75/0.99  inst_num_tautologies:                   0
% 2.75/0.99  inst_num_prop_implied:                  0
% 2.75/0.99  inst_num_existing_simplified:           0
% 2.75/0.99  inst_num_eq_res_simplified:             0
% 2.75/0.99  inst_num_child_elim:                    0
% 2.75/0.99  inst_num_of_dismatching_blockings:      4
% 2.75/0.99  inst_num_of_non_proper_insts:           388
% 2.75/0.99  inst_num_of_duplicates:                 0
% 2.75/0.99  inst_inst_num_from_inst_to_res:         0
% 2.75/0.99  inst_dismatching_checking_time:         0.
% 2.75/0.99  
% 2.75/0.99  ------ Resolution
% 2.75/0.99  
% 2.75/0.99  res_num_of_clauses:                     0
% 2.75/0.99  res_num_in_passive:                     0
% 2.75/0.99  res_num_in_active:                      0
% 2.75/0.99  res_num_of_loops:                       141
% 2.75/0.99  res_forward_subset_subsumed:            9
% 2.75/0.99  res_backward_subset_subsumed:           0
% 2.75/0.99  res_forward_subsumed:                   0
% 2.75/0.99  res_backward_subsumed:                  0
% 2.75/0.99  res_forward_subsumption_resolution:     0
% 2.75/0.99  res_backward_subsumption_resolution:    0
% 2.75/0.99  res_clause_to_clause_subsumption:       338
% 2.75/0.99  res_orphan_elimination:                 0
% 2.75/0.99  res_tautology_del:                      1
% 2.75/0.99  res_num_eq_res_simplified:              0
% 2.75/0.99  res_num_sel_changes:                    0
% 2.75/0.99  res_moves_from_active_to_pass:          0
% 2.75/0.99  
% 2.75/0.99  ------ Superposition
% 2.75/0.99  
% 2.75/0.99  sup_time_total:                         0.
% 2.75/0.99  sup_time_generating:                    0.
% 2.75/0.99  sup_time_sim_full:                      0.
% 2.75/0.99  sup_time_sim_immed:                     0.
% 2.75/0.99  
% 2.75/0.99  sup_num_of_clauses:                     85
% 2.75/0.99  sup_num_in_active:                      7
% 2.75/0.99  sup_num_in_passive:                     78
% 2.75/0.99  sup_num_of_loops:                       62
% 2.75/0.99  sup_fw_superposition:                   129
% 2.75/0.99  sup_bw_superposition:                   449
% 2.75/0.99  sup_immediate_simplified:               140
% 2.75/0.99  sup_given_eliminated:                   0
% 2.75/0.99  comparisons_done:                       0
% 2.75/0.99  comparisons_avoided:                    12
% 2.75/0.99  
% 2.75/0.99  ------ Simplifications
% 2.75/0.99  
% 2.75/0.99  
% 2.75/0.99  sim_fw_subset_subsumed:                 63
% 2.75/0.99  sim_bw_subset_subsumed:                 20
% 2.75/0.99  sim_fw_subsumed:                        48
% 2.75/0.99  sim_bw_subsumed:                        13
% 2.75/0.99  sim_fw_subsumption_res:                 0
% 2.75/0.99  sim_bw_subsumption_res:                 0
% 2.75/0.99  sim_tautology_del:                      8
% 2.75/0.99  sim_eq_tautology_del:                   39
% 2.75/0.99  sim_eq_res_simp:                        12
% 2.75/0.99  sim_fw_demodulated:                     18
% 2.75/0.99  sim_bw_demodulated:                     46
% 2.75/0.99  sim_light_normalised:                   11
% 2.75/0.99  sim_joinable_taut:                      0
% 2.75/0.99  sim_joinable_simp:                      0
% 2.75/0.99  sim_ac_normalised:                      0
% 2.75/0.99  sim_smt_subsumption:                    0
% 2.75/0.99  
%------------------------------------------------------------------------------
