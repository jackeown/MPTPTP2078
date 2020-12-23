%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t15_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:20 EDT 2019

% Result     : Theorem 150.33s
% Output     : Refutation 150.33s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 707 expanded)
%              Number of leaves         :   12 ( 219 expanded)
%              Depth                    :   24
%              Number of atoms          :  413 (6335 expanded)
%              Number of equality atoms :   42 ( 637 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31556,plain,(
    $false ),
    inference(subsumption_resolution,[],[f31555,f487])).

fof(f487,plain,(
    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f486,f59])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k4_subset_1(sK0,sK2,sK3) != sK1
    & ! [X4] :
        ( ( ( r2_hidden(X4,sK1)
            | ( ~ r2_hidden(X4,sK3)
              & ~ r2_hidden(X4,sK2) ) )
          & ( r2_hidden(X4,sK3)
            | r2_hidden(X4,sK2)
            | ~ r2_hidden(X4,sK1) ) )
        | ~ m1_subset_1(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k4_subset_1(X0,X2,X3) != X1
                & ! [X4] :
                    ( ( ( r2_hidden(X4,X1)
                        | ( ~ r2_hidden(X4,X3)
                          & ~ r2_hidden(X4,X2) ) )
                      & ( r2_hidden(X4,X3)
                        | r2_hidden(X4,X2)
                        | ~ r2_hidden(X4,X1) ) )
                    | ~ m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(sK0,X2,X3) != sK1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,sK1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,sK1) ) )
                  | ~ m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ? [X3] :
            ( k4_subset_1(X0,sK2,X3) != X1
            & ! [X4] :
                ( ( ( r2_hidden(X4,X1)
                    | ( ~ r2_hidden(X4,X3)
                      & ~ r2_hidden(X4,sK2) ) )
                  & ( r2_hidden(X4,X3)
                    | r2_hidden(X4,sK2)
                    | ~ r2_hidden(X4,X1) ) )
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k4_subset_1(X0,X2,X3) != X1
          & ! [X4] :
              ( ( ( r2_hidden(X4,X1)
                  | ( ~ r2_hidden(X4,X3)
                    & ~ r2_hidden(X4,X2) ) )
                & ( r2_hidden(X4,X3)
                  | r2_hidden(X4,X2)
                  | ~ r2_hidden(X4,X1) ) )
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( k4_subset_1(X0,X2,sK3) != X1
        & ! [X4] :
            ( ( ( r2_hidden(X4,X1)
                | ( ~ r2_hidden(X4,sK3)
                  & ~ r2_hidden(X4,X2) ) )
              & ( r2_hidden(X4,sK3)
                | r2_hidden(X4,X2)
                | ~ r2_hidden(X4,X1) ) )
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
                          | r2_hidden(X4,X2) ) ) )
                 => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
                        | r2_hidden(X4,X2) ) ) )
               => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',t15_subset_1)).

fof(f486,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f466,f58])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f466,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f133,f119])).

fof(f119,plain,(
    ! [X8] :
      ( k4_subset_1(sK0,sK2,X8) = k2_xboole_0(sK2,X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f58,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',redefinition_k4_subset_1)).

fof(f133,plain,(
    ! [X7] :
      ( m1_subset_1(k4_subset_1(sK0,X7,sK3),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f59,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',dt_k4_subset_1)).

fof(f31555,plain,(
    ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f31554,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',commutativity_k2_xboole_0)).

fof(f31554,plain,(
    ~ m1_subset_1(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f31553,f4221])).

fof(f4221,plain,(
    ~ r1_tarski(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4215,f143])).

fof(f143,plain,(
    k2_xboole_0(sK2,sK3) != sK1 ),
    inference(subsumption_resolution,[],[f142,f58])).

fof(f142,plain,
    ( k2_xboole_0(sK2,sK3) != sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f141,f59])).

fof(f141,plain,
    ( k2_xboole_0(sK2,sK3) != sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f63,f81])).

fof(f63,plain,(
    k4_subset_1(sK0,sK2,sK3) != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f4215,plain,
    ( k2_xboole_0(sK2,sK3) = sK1
    | ~ r1_tarski(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(resolution,[],[f4027,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',d10_xboole_0)).

fof(f4027,plain,(
    r1_tarski(k2_xboole_0(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f4026,f487])).

fof(f4026,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | r1_tarski(k2_xboole_0(sK2,sK3),sK1) ),
    inference(forward_demodulation,[],[f4025,f69])).

fof(f4025,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK3),sK1)
    | ~ m1_subset_1(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f4024,f69])).

fof(f4024,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK2),sK1)
    | ~ m1_subset_1(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f4023,f97])).

fof(f97,plain,(
    ! [X1] :
      ( m1_subset_1(sK5(sK0,X1,sK1),sK0)
      | r1_tarski(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f57,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK5(X0,X1,X2),X2)
            & r2_hidden(sK5(X0,X1,X2),X1)
            & m1_subset_1(sK5(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',t7_subset_1)).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f4023,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK2),sK1)
    | ~ m1_subset_1(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK5(sK0,k2_xboole_0(sK3,sK2),sK1),sK0) ),
    inference(subsumption_resolution,[],[f3951,f101])).

fof(f101,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK5(sK0,X5,sK1),sK1)
      | r1_tarski(X5,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f57,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3951,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK2),sK1)
    | ~ m1_subset_1(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK0))
    | r2_hidden(sK5(sK0,k2_xboole_0(sK3,sK2),sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,k2_xboole_0(sK3,sK2),sK1),sK0) ),
    inference(resolution,[],[f974,f62])).

fof(f62,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK3)
      | r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f974,plain,(
    ! [X7] :
      ( r2_hidden(sK5(sK0,k2_xboole_0(X7,sK2),sK1),X7)
      | r1_tarski(k2_xboole_0(X7,sK2),sK1)
      | ~ m1_subset_1(k2_xboole_0(X7,sK2),k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f973,f101])).

fof(f973,plain,(
    ! [X7] :
      ( r2_hidden(sK5(sK0,k2_xboole_0(X7,sK2),sK1),X7)
      | r2_hidden(sK5(sK0,k2_xboole_0(X7,sK2),sK1),sK1)
      | r1_tarski(k2_xboole_0(X7,sK2),sK1)
      | ~ m1_subset_1(k2_xboole_0(X7,sK2),k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f959,f97])).

fof(f959,plain,(
    ! [X7] :
      ( ~ m1_subset_1(sK5(sK0,k2_xboole_0(X7,sK2),sK1),sK0)
      | r2_hidden(sK5(sK0,k2_xboole_0(X7,sK2),sK1),X7)
      | r2_hidden(sK5(sK0,k2_xboole_0(X7,sK2),sK1),sK1)
      | r1_tarski(k2_xboole_0(X7,sK2),sK1)
      | ~ m1_subset_1(k2_xboole_0(X7,sK2),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f151,f99])).

fof(f99,plain,(
    ! [X3] :
      ( r2_hidden(sK5(sK0,X3,sK1),X3)
      | r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f57,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f151,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,k2_xboole_0(X9,sK2))
      | ~ m1_subset_1(X8,sK0)
      | r2_hidden(X8,X9)
      | r2_hidden(X8,sK1) ) ),
    inference(resolution,[],[f61,f93])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & ~ r2_hidden(sK6(X0,X1,X2),X0) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & ~ r2_hidden(sK6(X0,X1,X2),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t15_subset_1.p',d3_xboole_0)).

fof(f61,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f31553,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f31552,f69])).

fof(f31552,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK3,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f31551,f4221])).

fof(f31551,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK3,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f31529,f487])).

fof(f31529,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK3,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK3,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(resolution,[],[f3549,f3547])).

fof(f3547,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(sK5(sK0,sK1,k2_xboole_0(X12,X11)),X11)
      | ~ m1_subset_1(k2_xboole_0(X11,X12),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k2_xboole_0(X11,X12)) ) ),
    inference(superposition,[],[f679,f69])).

fof(f679,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK5(sK0,sK1,k2_xboole_0(X4,X5)),X4)
      | ~ m1_subset_1(k2_xboole_0(X4,X5),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k2_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f100,f92])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f100,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK5(sK0,sK1,X4),X4)
      | r1_tarski(sK1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f57,f73])).

fof(f3549,plain,(
    ! [X18] :
      ( r2_hidden(sK5(sK0,sK1,k2_xboole_0(sK3,X18)),sK2)
      | r1_tarski(sK1,k2_xboole_0(sK3,X18))
      | ~ m1_subset_1(k2_xboole_0(sK3,X18),k1_zfmisc_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f3541])).

fof(f3541,plain,(
    ! [X18] :
      ( ~ m1_subset_1(k2_xboole_0(sK3,X18),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k2_xboole_0(sK3,X18))
      | ~ m1_subset_1(k2_xboole_0(sK3,X18),k1_zfmisc_1(sK0))
      | r2_hidden(sK5(sK0,sK1,k2_xboole_0(sK3,X18)),sK2)
      | r1_tarski(sK1,k2_xboole_0(sK3,X18)) ) ),
    inference(resolution,[],[f679,f645])).

fof(f645,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK0,sK1,X0),sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(sK5(sK0,sK1,X0),sK2)
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f638,f96])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,X0),sK0)
      | r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f57,f71])).

fof(f638,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r2_hidden(sK5(sK0,sK1,X0),sK2)
      | r2_hidden(sK5(sK0,sK1,X0),sK3)
      | ~ m1_subset_1(sK5(sK0,sK1,X0),sK0) ) ),
    inference(resolution,[],[f98,f60])).

fof(f60,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,sK2)
      | r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    ! [X2] :
      ( r2_hidden(sK5(sK0,sK1,X2),sK1)
      | r1_tarski(sK1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f57,f72])).
%------------------------------------------------------------------------------
