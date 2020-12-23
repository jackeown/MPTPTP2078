%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0349+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    9
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1458,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1457,f827])).

fof(f827,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f486])).

fof(f486,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1457,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) ),
    inference(subsumption_resolution,[],[f1454,f933])).

fof(f933,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1454,plain,
    ( sK5 != k4_xboole_0(sK5,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) ),
    inference(superposition,[],[f1412,f810])).

fof(f810,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f495])).

fof(f495,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f457])).

fof(f457,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1412,plain,(
    sK5 != k3_subset_1(sK5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1204,f816])).

fof(f816,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f1204,plain,(
    k2_subset_1(sK5) != k3_subset_1(sK5,k1_xboole_0) ),
    inference(definition_unfolding,[],[f808,f813])).

fof(f813,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f455])).

fof(f455,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f808,plain,(
    k2_subset_1(sK5) != k3_subset_1(sK5,k1_subset_1(sK5)) ),
    inference(cnf_transformation,[],[f689])).

fof(f689,plain,(
    k2_subset_1(sK5) != k3_subset_1(sK5,k1_subset_1(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f493,f688])).

fof(f688,plain,
    ( ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0))
   => k2_subset_1(sK5) != k3_subset_1(sK5,k1_subset_1(sK5)) ),
    introduced(choice_axiom,[])).

fof(f493,plain,(
    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(ennf_transformation,[],[f485])).

fof(f485,negated_conjecture,(
    ~ ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(negated_conjecture,[],[f484])).

fof(f484,conjecture,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
%------------------------------------------------------------------------------
