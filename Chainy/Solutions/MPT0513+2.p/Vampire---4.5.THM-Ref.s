%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0513+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:34 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 (  89 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2027,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1931,f1936,f1965,f2026])).

fof(f2026,plain,
    ( ~ spl86_3
    | spl86_8 ),
    inference(avatar_contradiction_clause,[],[f2025])).

fof(f2025,plain,
    ( $false
    | ~ spl86_3
    | spl86_8 ),
    inference(subsumption_resolution,[],[f2024,f1288])).

fof(f1288,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2024,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl86_3
    | spl86_8 ),
    inference(backward_demodulation,[],[f1964,f2021])).

fof(f2021,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl86_3 ),
    inference(forward_demodulation,[],[f2016,f2005])).

fof(f2005,plain,
    ( k1_xboole_0 = k7_relat_1(sK17,k1_xboole_0)
    | ~ spl86_3 ),
    inference(unit_resulting_resolution,[],[f1935,f1258])).

fof(f1258,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f795])).

fof(f795,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f685])).

fof(f685,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f1935,plain,
    ( v1_relat_1(sK17)
    | ~ spl86_3 ),
    inference(avatar_component_clause,[],[f1933])).

fof(f1933,plain,
    ( spl86_3
  <=> v1_relat_1(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl86_3])])).

fof(f2016,plain,
    ( ! [X0] : k7_relat_1(sK17,k1_xboole_0) = k7_relat_1(k7_relat_1(sK17,k1_xboole_0),X0)
    | ~ spl86_3 ),
    inference(unit_resulting_resolution,[],[f1935,f1288,f1230])).

fof(f1230,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f768])).

fof(f768,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f767])).

fof(f767,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f677])).

fof(f677,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(f1964,plain,
    ( ~ r1_tarski(k7_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | spl86_8 ),
    inference(avatar_component_clause,[],[f1962])).

fof(f1962,plain,
    ( spl86_8
  <=> r1_tarski(k7_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl86_8])])).

fof(f1965,plain,
    ( ~ spl86_8
    | spl86_2 ),
    inference(avatar_split_clause,[],[f1958,f1928,f1962])).

fof(f1928,plain,
    ( spl86_2
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl86_2])])).

fof(f1958,plain,
    ( ~ r1_tarski(k7_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | spl86_2 ),
    inference(unit_resulting_resolution,[],[f1930,f1284])).

fof(f1284,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f806])).

fof(f806,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f1930,plain,
    ( k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)
    | spl86_2 ),
    inference(avatar_component_clause,[],[f1928])).

fof(f1936,plain,(
    spl86_3 ),
    inference(avatar_split_clause,[],[f1372,f1933])).

fof(f1372,plain,(
    v1_relat_1(sK17) ),
    inference(cnf_transformation,[],[f1082])).

fof(f1082,plain,
    ( v1_relat_1(sK17)
    & ~ v1_xboole_0(sK17) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f674,f1081])).

fof(f1081,plain,
    ( ? [X0] :
        ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_relat_1(sK17)
      & ~ v1_xboole_0(sK17) ) ),
    introduced(choice_axiom,[])).

fof(f674,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relat_1)).

fof(f1931,plain,(
    ~ spl86_2 ),
    inference(avatar_split_clause,[],[f1225,f1928])).

fof(f1225,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f1029])).

fof(f1029,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f763,f1028])).

fof(f1028,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f763,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f687])).

fof(f687,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f686])).

fof(f686,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
