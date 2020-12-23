%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0357+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  54 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 ( 174 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1317,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1316,f1237])).

fof(f1237,plain,(
    r1_tarski(sK5,k2_xboole_0(sK6,sK7)) ),
    inference(resolution,[],[f1193,f790])).

fof(f790,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f538])).

fof(f538,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f106,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1193,plain,(
    r1_tarski(k4_xboole_0(sK5,sK6),sK7) ),
    inference(backward_demodulation,[],[f725,f1174])).

fof(f1174,plain,(
    k3_subset_1(sK5,sK6) = k4_xboole_0(sK5,sK6) ),
    inference(resolution,[],[f723,f747])).

fof(f747,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f525])).

fof(f525,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f458])).

fof(f458,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f723,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f624])).

fof(f624,plain,
    ( ~ r1_tarski(k3_subset_1(sK5,sK7),sK6)
    & r1_tarski(k3_subset_1(sK5,sK6),sK7)
    & m1_subset_1(sK7,k1_zfmisc_1(sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f506,f623,f622])).

fof(f622,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
            & r1_tarski(k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK5,X2),sK6)
          & r1_tarski(k3_subset_1(sK5,sK6),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f623,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK5,X2),sK6)
        & r1_tarski(k3_subset_1(sK5,sK6),X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK5)) )
   => ( ~ r1_tarski(k3_subset_1(sK5,sK7),sK6)
      & r1_tarski(k3_subset_1(sK5,sK6),sK7)
      & m1_subset_1(sK7,k1_zfmisc_1(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f506,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f505])).

fof(f505,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f499])).

fof(f499,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f498])).

fof(f498,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

fof(f725,plain,(
    r1_tarski(k3_subset_1(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f624])).

fof(f1316,plain,(
    ~ r1_tarski(sK5,k2_xboole_0(sK6,sK7)) ),
    inference(forward_demodulation,[],[f1300,f775])).

fof(f775,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1300,plain,(
    ~ r1_tarski(sK5,k2_xboole_0(sK7,sK6)) ),
    inference(resolution,[],[f1228,f791])).

fof(f791,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f539])).

fof(f539,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f105])).

fof(f105,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1228,plain,(
    ~ r1_tarski(k4_xboole_0(sK5,sK7),sK6) ),
    inference(backward_demodulation,[],[f726,f1209])).

fof(f1209,plain,(
    k3_subset_1(sK5,sK7) = k4_xboole_0(sK5,sK7) ),
    inference(resolution,[],[f724,f747])).

fof(f724,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f624])).

fof(f726,plain,(
    ~ r1_tarski(k3_subset_1(sK5,sK7),sK6) ),
    inference(cnf_transformation,[],[f624])).
%------------------------------------------------------------------------------
