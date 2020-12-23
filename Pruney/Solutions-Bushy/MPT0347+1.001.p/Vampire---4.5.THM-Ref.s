%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0347+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:47 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 399 expanded)
%              Number of leaves         :   11 ( 122 expanded)
%              Depth                    :   20
%              Number of atoms          :  404 (3513 expanded)
%              Number of equality atoms :   38 ( 341 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2165,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2164,f2103])).

fof(f2103,plain,(
    r1_tarski(k4_xboole_0(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f2101,f117])).

fof(f117,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f116,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != k7_subset_1(sK0,sK2,sK3)
    & ! [X4] :
        ( ( ( r2_hidden(X4,sK1)
            | r2_hidden(X4,sK3)
            | ~ r2_hidden(X4,sK2) )
          & ( ( ~ r2_hidden(X4,sK3)
              & r2_hidden(X4,sK2) )
            | ~ r2_hidden(X4,sK1) ) )
        | ~ m1_subset_1(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k7_subset_1(X0,X2,X3) != X1
                & ! [X4] :
                    ( ( ( r2_hidden(X4,X1)
                        | r2_hidden(X4,X3)
                        | ~ r2_hidden(X4,X2) )
                      & ( ( ~ r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) )
                        | ~ r2_hidden(X4,X1) ) )
                    | ~ m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( sK1 != k7_subset_1(sK0,X2,X3)
              & ! [X4] :
                  ( ( ( r2_hidden(X4,sK1)
                      | r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( ~ r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,sK1) ) )
                  | ~ m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( sK1 != k7_subset_1(sK0,X2,X3)
            & ! [X4] :
                ( ( ( r2_hidden(X4,sK1)
                    | r2_hidden(X4,X3)
                    | ~ r2_hidden(X4,X2) )
                  & ( ( ~ r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) )
                    | ~ r2_hidden(X4,sK1) ) )
                | ~ m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ? [X3] :
          ( sK1 != k7_subset_1(sK0,sK2,X3)
          & ! [X4] :
              ( ( ( r2_hidden(X4,sK1)
                  | r2_hidden(X4,X3)
                  | ~ r2_hidden(X4,sK2) )
                & ( ( ~ r2_hidden(X4,X3)
                    & r2_hidden(X4,sK2) )
                  | ~ r2_hidden(X4,sK1) ) )
              | ~ m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( sK1 != k7_subset_1(sK0,sK2,X3)
        & ! [X4] :
            ( ( ( r2_hidden(X4,sK1)
                | r2_hidden(X4,X3)
                | ~ r2_hidden(X4,sK2) )
              & ( ( ~ r2_hidden(X4,X3)
                  & r2_hidden(X4,sK2) )
                | ~ r2_hidden(X4,sK1) ) )
            | ~ m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( sK1 != k7_subset_1(sK0,sK2,sK3)
      & ! [X4] :
          ( ( ( r2_hidden(X4,sK1)
              | r2_hidden(X4,sK3)
              | ~ r2_hidden(X4,sK2) )
            & ( ( ~ r2_hidden(X4,sK3)
                & r2_hidden(X4,sK2) )
              | ~ r2_hidden(X4,sK1) ) )
          | ~ m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( ~ r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( ~ r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( ~ r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( ~ r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,X1)
                      <=> ( ~ r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) ) ) )
                 => k7_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( ~ r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) ) ) )
               => k7_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_subset_1)).

fof(f116,plain,(
    ! [X0] :
      ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f69,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f69,plain,(
    ! [X6] : m1_subset_1(k7_subset_1(sK0,sK2,X6),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f2101,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f2095])).

fof(f2095,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK3),sK1)
    | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | r1_tarski(k4_xboole_0(sK2,sK3),sK1) ),
    inference(resolution,[],[f1399,f172])).

fof(f172,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK4(sK0,k4_xboole_0(X6,X7),sK1),X7)
      | ~ m1_subset_1(k4_xboole_0(X6,X7),k1_zfmisc_1(sK0))
      | r1_tarski(k4_xboole_0(X6,X7),sK1) ) ),
    inference(resolution,[],[f58,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f58,plain,(
    ! [X3] :
      ( r2_hidden(sK4(sK0,X3,sK1),X3)
      | r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f29,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK4(X0,X1,X2),X2)
            & r2_hidden(sK4(X0,X1,X2),X1)
            & m1_subset_1(sK4(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f1399,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(sK2,X0),sK1),sK3)
      | r1_tarski(k4_xboole_0(sK2,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f1392,f117])).

fof(f1392,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK0))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK2,X0),sK1),sK3)
      | r1_tarski(k4_xboole_0(sK2,X0),sK1) ) ),
    inference(duplicate_literal_removal,[],[f1387])).

fof(f1387,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK0))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK2,X0),sK1),sK3)
      | r1_tarski(k4_xboole_0(sK2,X0),sK1)
      | ~ m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK0))
      | r1_tarski(k4_xboole_0(sK2,X0),sK1) ) ),
    inference(resolution,[],[f1377,f171])).

fof(f171,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(X4,X5),sK1),X4)
      | ~ m1_subset_1(k4_xboole_0(X4,X5),k1_zfmisc_1(sK0))
      | r1_tarski(k4_xboole_0(X4,X5),sK1) ) ),
    inference(resolution,[],[f58,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1377,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,X0,sK1),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(sK4(sK0,X0,sK1),sK3)
      | r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f161,f60])).

fof(f60,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4(sK0,X5,sK1),sK1)
      | r1_tarski(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f29,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f161,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(sK4(sK0,X0,sK1),sK3)
      | ~ r2_hidden(sK4(sK0,X0,sK1),sK2)
      | r2_hidden(sK4(sK0,X0,sK1),sK1) ) ),
    inference(resolution,[],[f56,f34])).

fof(f34,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | r2_hidden(X4,sK3)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK0,X1,sK1),sK0)
      | r1_tarski(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f29,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2164,plain,(
    ~ r1_tarski(k4_xboole_0(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f2159,f80])).

fof(f80,plain,(
    sK1 != k4_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f79,f30])).

fof(f79,plain,
    ( sK1 != k4_xboole_0(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f35,f43])).

fof(f35,plain,(
    sK1 != k7_subset_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f2159,plain,
    ( sK1 = k4_xboole_0(sK2,sK3)
    | ~ r1_tarski(k4_xboole_0(sK2,sK3),sK1) ),
    inference(resolution,[],[f2156,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2156,plain,(
    r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f2145,f117])).

fof(f2145,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f2135])).

fof(f2135,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(resolution,[],[f1564,f790])).

fof(f790,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(sK0,sK1,X1),sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f159,f57])).

fof(f57,plain,(
    ! [X2] :
      ( r2_hidden(sK4(sK0,sK1,X2),sK1)
      | r1_tarski(sK1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f29,f37])).

fof(f159,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK4(sK0,sK1,X1),sK1)
      | ~ r2_hidden(sK4(sK0,sK1,X1),sK3) ) ),
    inference(resolution,[],[f55,f33])).

fof(f33,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,sK1,X0),sK0)
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f29,f36])).

fof(f1564,plain,(
    ! [X14] :
      ( r2_hidden(sK4(sK0,sK1,k4_xboole_0(sK2,X14)),X14)
      | r1_tarski(sK1,k4_xboole_0(sK2,X14)) ) ),
    inference(subsumption_resolution,[],[f1553,f117])).

fof(f1553,plain,(
    ! [X14] :
      ( ~ m1_subset_1(k4_xboole_0(sK2,X14),k1_zfmisc_1(sK0))
      | r2_hidden(sK4(sK0,sK1,k4_xboole_0(sK2,X14)),X14)
      | r1_tarski(sK1,k4_xboole_0(sK2,X14)) ) ),
    inference(duplicate_literal_removal,[],[f1549])).

fof(f1549,plain,(
    ! [X14] :
      ( ~ m1_subset_1(k4_xboole_0(sK2,X14),k1_zfmisc_1(sK0))
      | r2_hidden(sK4(sK0,sK1,k4_xboole_0(sK2,X14)),X14)
      | r1_tarski(sK1,k4_xboole_0(sK2,X14))
      | r1_tarski(sK1,k4_xboole_0(sK2,X14))
      | ~ m1_subset_1(k4_xboole_0(sK2,X14),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f178,f336])).

fof(f336,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f335,f29])).

fof(f335,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f81,f57])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),sK1)
      | r2_hidden(sK4(sK0,X0,X1),sK2)
      | r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f32,f36])).

fof(f32,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f178,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK4(sK0,sK1,k4_xboole_0(X4,X5)),X4)
      | ~ m1_subset_1(k4_xboole_0(X4,X5),k1_zfmisc_1(sK0))
      | r2_hidden(sK4(sK0,sK1,k4_xboole_0(X4,X5)),X5)
      | r1_tarski(sK1,k4_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f59,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK4(sK0,sK1,X4),X4)
      | r1_tarski(sK1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f29,f38])).

%------------------------------------------------------------------------------
