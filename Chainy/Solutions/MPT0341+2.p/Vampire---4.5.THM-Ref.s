%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0341+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:25 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   22 (  26 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  44 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f733,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f698,f732])).

fof(f732,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f729])).

fof(f729,plain,
    ( $false
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f697,f727])).

fof(f727,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f537,f724])).

fof(f724,plain,(
    ! [X0] : k1_xboole_0 = sK1(X0) ),
    inference(unit_resulting_resolution,[],[f538,f645])).

fof(f645,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f494])).

fof(f494,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f538,plain,(
    ! [X0] : v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f500])).

fof(f500,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1(X0))
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f458,f499])).

fof(f499,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f458,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f537,plain,(
    ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f500])).

fof(f697,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f695])).

fof(f695,plain,
    ( spl8_1
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f698,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f536,f695])).

fof(f536,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f498])).

fof(f498,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f462,f497])).

fof(f497,plain,
    ( ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
   => ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f462,plain,(
    ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(ennf_transformation,[],[f460])).

fof(f460,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(negated_conjecture,[],[f459])).

fof(f459,conjecture,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
%------------------------------------------------------------------------------
