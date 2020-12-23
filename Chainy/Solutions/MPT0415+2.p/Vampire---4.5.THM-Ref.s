%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0415+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   64 (  95 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :   16
%              Number of atoms          :  204 ( 300 expanded)
%              Number of equality atoms :   49 ( 110 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1606,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1605,f698])).

fof(f698,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f646])).

fof(f646,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f605,f645])).

fof(f645,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f605,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f604])).

fof(f604,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f595])).

fof(f595,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f594])).

fof(f594,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f1605,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1593,f697])).

fof(f697,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f646])).

fof(f1593,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f910,f1290])).

fof(f1290,plain,(
    ~ m1_subset_1(sK6(sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f1284,f698])).

fof(f1284,plain,
    ( ~ m1_subset_1(sK6(sK1),k1_zfmisc_1(sK0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1189,f767])).

fof(f767,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f675])).

fof(f675,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f627,f674])).

fof(f674,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f627,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f1189,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f1188,f774])).

fof(f774,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1188,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f1186,f1033])).

fof(f1033,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1030,f833])).

fof(f833,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f766,f770])).

fof(f770,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f766,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f407])).

fof(f407,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f1030,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | k1_xboole_0 = k1_tarski(X2) ) ),
    inference(resolution,[],[f881,f768])).

fof(f768,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f628])).

fof(f628,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f881,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f794,f778])).

fof(f778,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f676])).

fof(f676,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f590])).

fof(f590,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f794,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f642])).

fof(f642,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f535])).

fof(f535,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f1186,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(superposition,[],[f829,f964])).

fof(f964,plain,(
    sK1 = k7_setfam_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f961,f699])).

fof(f699,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f646])).

fof(f961,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f706,f697])).

fof(f706,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f608])).

fof(f608,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f561])).

fof(f561,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f829,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(subsumption_resolution,[],[f806,f705])).

fof(f705,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f607])).

fof(f607,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f557])).

fof(f557,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f806,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f700])).

fof(f700,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f651])).

fof(f651,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
                  | r2_hidden(sK2(X0,X1,X2),X2) )
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f649,f650])).

fof(f650,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f649,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f648])).

fof(f648,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f647])).

fof(f647,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f606])).

fof(f606,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f552])).

fof(f552,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f910,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f777,f767])).

fof(f777,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f630])).

fof(f630,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f629])).

fof(f629,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f597])).

fof(f597,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
%------------------------------------------------------------------------------
