%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0346+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:47 EST 2020

% Result     : Theorem 2.92s
% Output     : Refutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 415 expanded)
%              Number of leaves         :   12 ( 127 expanded)
%              Depth                    :   21
%              Number of atoms          :  421 (3533 expanded)
%              Number of equality atoms :   41 ( 354 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3270,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3269,f3157])).

fof(f3157,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),sK1) ),
    inference(forward_demodulation,[],[f3156,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f3156,plain,(
    r1_tarski(k3_xboole_0(sK3,sK2),sK1) ),
    inference(subsumption_resolution,[],[f3155,f170])).

fof(f170,plain,(
    ! [X6] : m1_subset_1(k3_xboole_0(sK3,X6),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f154,f40])).

fof(f154,plain,(
    ! [X6] : m1_subset_1(k3_xboole_0(X6,sK3),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f82,f83])).

fof(f83,plain,(
    ! [X7] : k9_subset_1(sK0,X7,sK3) = k3_xboole_0(X7,sK3) ),
    inference(resolution,[],[f34,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != k9_subset_1(sK0,sK2,sK3)
    & ! [X4] :
        ( ( ( r2_hidden(X4,sK1)
            | ~ r2_hidden(X4,sK3)
            | ~ r2_hidden(X4,sK2) )
          & ( ( r2_hidden(X4,sK3)
              & r2_hidden(X4,sK2) )
            | ~ r2_hidden(X4,sK1) ) )
        | ~ m1_subset_1(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k9_subset_1(X0,X2,X3) != X1
                & ! [X4] :
                    ( ( ( r2_hidden(X4,X1)
                        | ~ r2_hidden(X4,X3)
                        | ~ r2_hidden(X4,X2) )
                      & ( ( r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) )
                        | ~ r2_hidden(X4,X1) ) )
                    | ~ m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( sK1 != k9_subset_1(sK0,X2,X3)
              & ! [X4] :
                  ( ( ( r2_hidden(X4,sK1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,sK1) ) )
                  | ~ m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( sK1 != k9_subset_1(sK0,X2,X3)
            & ! [X4] :
                ( ( ( r2_hidden(X4,sK1)
                    | ~ r2_hidden(X4,X3)
                    | ~ r2_hidden(X4,X2) )
                  & ( ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) )
                    | ~ r2_hidden(X4,sK1) ) )
                | ~ m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ? [X3] :
          ( sK1 != k9_subset_1(sK0,sK2,X3)
          & ! [X4] :
              ( ( ( r2_hidden(X4,sK1)
                  | ~ r2_hidden(X4,X3)
                  | ~ r2_hidden(X4,sK2) )
                & ( ( r2_hidden(X4,X3)
                    & r2_hidden(X4,sK2) )
                  | ~ r2_hidden(X4,sK1) ) )
              | ~ m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( sK1 != k9_subset_1(sK0,sK2,X3)
        & ! [X4] :
            ( ( ( r2_hidden(X4,sK1)
                | ~ r2_hidden(X4,X3)
                | ~ r2_hidden(X4,sK2) )
              & ( ( r2_hidden(X4,X3)
                  & r2_hidden(X4,sK2) )
                | ~ r2_hidden(X4,sK1) ) )
            | ~ m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( sK1 != k9_subset_1(sK0,sK2,sK3)
      & ! [X4] :
          ( ( ( r2_hidden(X4,sK1)
              | ~ r2_hidden(X4,sK3)
              | ~ r2_hidden(X4,sK2) )
            & ( ( r2_hidden(X4,sK3)
                & r2_hidden(X4,sK2) )
              | ~ r2_hidden(X4,sK1) ) )
          | ~ m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,X3)
                      | ~ r2_hidden(X4,X2) )
                    & ( ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) )
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k9_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,X1)
                      <=> ( r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) ) ) )
                 => k9_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) ) ) )
               => k9_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_subset_1)).

fof(f82,plain,(
    ! [X6] : m1_subset_1(k9_subset_1(sK0,X6,sK3),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f3155,plain,
    ( r1_tarski(k3_xboole_0(sK3,sK2),sK1)
    | ~ m1_subset_1(k3_xboole_0(sK3,sK2),k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f3146])).

fof(f3146,plain,
    ( r1_tarski(k3_xboole_0(sK3,sK2),sK1)
    | ~ m1_subset_1(k3_xboole_0(sK3,sK2),k1_zfmisc_1(sK0))
    | r1_tarski(k3_xboole_0(sK3,sK2),sK1) ),
    inference(resolution,[],[f1774,f186])).

fof(f186,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK4(sK0,k3_xboole_0(X6,X7),sK1),X7)
      | ~ m1_subset_1(k3_xboole_0(X6,X7),k1_zfmisc_1(sK0))
      | r1_tarski(k3_xboole_0(X6,X7),sK1) ) ),
    inference(resolution,[],[f63,f58])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f63,plain,(
    ! [X3] :
      ( r2_hidden(sK4(sK0,X3,sK1),X3)
      | r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK4(X0,X1,X2),X2)
            & r2_hidden(sK4(X0,X1,X2),X1)
            & m1_subset_1(sK4(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f1774,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK3,X0),sK1),sK2)
      | r1_tarski(k3_xboole_0(sK3,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f1767,f170])).

fof(f1767,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k3_xboole_0(sK3,X0),k1_zfmisc_1(sK0))
      | r1_tarski(k3_xboole_0(sK3,X0),sK1)
      | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK3,X0),sK1),sK2) ) ),
    inference(duplicate_literal_removal,[],[f1760])).

fof(f1760,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k3_xboole_0(sK3,X0),k1_zfmisc_1(sK0))
      | r1_tarski(k3_xboole_0(sK3,X0),sK1)
      | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK3,X0),sK1),sK2)
      | ~ m1_subset_1(k3_xboole_0(sK3,X0),k1_zfmisc_1(sK0))
      | r1_tarski(k3_xboole_0(sK3,X0),sK1) ) ),
    inference(resolution,[],[f1742,f185])).

fof(f185,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(sK0,k3_xboole_0(X4,X5),sK1),X4)
      | ~ m1_subset_1(k3_xboole_0(X4,X5),k1_zfmisc_1(sK0))
      | r1_tarski(k3_xboole_0(X4,X5),sK1) ) ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1742,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,X0,sK1),sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(X0,sK1)
      | ~ r2_hidden(sK4(sK0,X0,sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f175,f65])).

fof(f65,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4(sK0,X5,sK1),sK1)
      | r1_tarski(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f32,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f175,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK4(sK0,X0,sK1),sK3)
      | ~ r2_hidden(sK4(sK0,X0,sK1),sK2)
      | r2_hidden(sK4(sK0,X0,sK1),sK1) ) ),
    inference(resolution,[],[f61,f37])).

fof(f37,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK0,X1,sK1),sK0)
      | r1_tarski(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f32,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3269,plain,(
    ~ r1_tarski(k3_xboole_0(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f3264,f85])).

fof(f85,plain,(
    sK1 != k3_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f84,f34])).

fof(f84,plain,
    ( sK1 != k3_xboole_0(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f38,f48])).

fof(f38,plain,(
    sK1 != k9_subset_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f3264,plain,
    ( sK1 = k3_xboole_0(sK2,sK3)
    | ~ r1_tarski(k3_xboole_0(sK2,sK3),sK1) ),
    inference(resolution,[],[f3220,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3220,plain,(
    r1_tarski(sK1,k3_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f3219,f40])).

fof(f3219,plain,(
    r1_tarski(sK1,k3_xboole_0(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f3194,f170])).

fof(f3194,plain,
    ( r1_tarski(sK1,k3_xboole_0(sK3,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK3,sK2),k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f3186])).

fof(f3186,plain,
    ( r1_tarski(sK1,k3_xboole_0(sK3,sK2))
    | r1_tarski(sK1,k3_xboole_0(sK3,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK3,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f2145,f343])).

fof(f343,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,sK1,X0),sK3)
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f342,f32])).

fof(f342,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,sK1,X0),sK3)
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,sK1,X0),sK3)
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f90,f62])).

fof(f62,plain,(
    ! [X2] :
      ( r2_hidden(sK4(sK0,sK1,X2),sK1)
      | r1_tarski(sK1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f32,f42])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),sK1)
      | r2_hidden(sK4(sK0,X0,X1),sK3)
      | r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f36,f41])).

fof(f36,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2145,plain,(
    ! [X16] :
      ( ~ r2_hidden(sK4(sK0,sK1,k3_xboole_0(X16,sK2)),X16)
      | r1_tarski(sK1,k3_xboole_0(X16,sK2)) ) ),
    inference(subsumption_resolution,[],[f2133,f125])).

fof(f125,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f124,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f124,plain,(
    ! [X0] :
      ( m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f74,f48])).

fof(f74,plain,(
    ! [X6] : m1_subset_1(k9_subset_1(sK0,X6,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f33,f47])).

fof(f2133,plain,(
    ! [X16] :
      ( ~ m1_subset_1(k3_xboole_0(X16,sK2),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k3_xboole_0(X16,sK2))
      | ~ r2_hidden(sK4(sK0,sK1,k3_xboole_0(X16,sK2)),X16) ) ),
    inference(duplicate_literal_removal,[],[f2123])).

fof(f2123,plain,(
    ! [X16] :
      ( ~ m1_subset_1(k3_xboole_0(X16,sK2),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k3_xboole_0(X16,sK2))
      | ~ r2_hidden(sK4(sK0,sK1,k3_xboole_0(X16,sK2)),X16)
      | r1_tarski(sK1,k3_xboole_0(X16,sK2))
      | ~ m1_subset_1(k3_xboole_0(X16,sK2),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f192,f325])).

fof(f325,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f324,f32])).

fof(f324,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,sK1,X0),sK2)
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f86,f62])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),sK1)
      | r2_hidden(sK4(sK0,X0,X1),sK2)
      | r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f35,f41])).

fof(f35,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f192,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK4(sK0,sK1,k3_xboole_0(X4,X5)),X5)
      | ~ m1_subset_1(k3_xboole_0(X4,X5),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k3_xboole_0(X4,X5))
      | ~ r2_hidden(sK4(sK0,sK1,k3_xboole_0(X4,X5)),X4) ) ),
    inference(resolution,[],[f64,f57])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK4(sK0,sK1,X4),X4)
      | r1_tarski(sK1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f32,f43])).

%------------------------------------------------------------------------------
