%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0471+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:31 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 (  88 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1846,f1871,f1924,f1929,f2123,f2256])).

fof(f2256,plain,
    ( spl91_1
    | ~ spl91_10
    | ~ spl91_11
    | ~ spl91_14 ),
    inference(avatar_contradiction_clause,[],[f2255])).

fof(f2255,plain,
    ( $false
    | spl91_1
    | ~ spl91_10
    | ~ spl91_11
    | ~ spl91_14 ),
    inference(subsumption_resolution,[],[f2254,f1845])).

fof(f1845,plain,
    ( k1_xboole_0 != k3_relat_1(k1_xboole_0)
    | spl91_1 ),
    inference(avatar_component_clause,[],[f1843])).

fof(f1843,plain,
    ( spl91_1
  <=> k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_1])])).

fof(f2254,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl91_10
    | ~ spl91_11
    | ~ spl91_14 ),
    inference(forward_demodulation,[],[f2253,f1923])).

fof(f1923,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl91_10 ),
    inference(avatar_component_clause,[],[f1921])).

fof(f1921,plain,
    ( spl91_10
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_10])])).

fof(f2253,plain,
    ( k1_relat_1(k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ spl91_11
    | ~ spl91_14 ),
    inference(forward_demodulation,[],[f2252,f1192])).

fof(f1192,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f2252,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl91_11
    | ~ spl91_14 ),
    inference(forward_demodulation,[],[f2245,f1928])).

fof(f1928,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl91_11 ),
    inference(avatar_component_clause,[],[f1926])).

fof(f1926,plain,
    ( spl91_11
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_11])])).

fof(f2245,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl91_14 ),
    inference(unit_resulting_resolution,[],[f2122,f1163])).

fof(f1163,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f717])).

fof(f717,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f645])).

fof(f645,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f2122,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl91_14 ),
    inference(avatar_component_clause,[],[f2120])).

fof(f2120,plain,
    ( spl91_14
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_14])])).

fof(f2123,plain,
    ( spl91_14
    | ~ spl91_6 ),
    inference(avatar_split_clause,[],[f2054,f1868,f2120])).

fof(f1868,plain,
    ( spl91_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_6])])).

fof(f2054,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl91_6 ),
    inference(unit_resulting_resolution,[],[f1870,f1592])).

fof(f1592,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f911])).

fof(f911,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f1870,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl91_6 ),
    inference(avatar_component_clause,[],[f1868])).

fof(f1929,plain,(
    spl91_11 ),
    inference(avatar_split_clause,[],[f1441,f1926])).

fof(f1441,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f703])).

fof(f703,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f1924,plain,(
    spl91_10 ),
    inference(avatar_split_clause,[],[f1440,f1921])).

fof(f1440,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f703])).

fof(f1871,plain,(
    spl91_6 ),
    inference(avatar_split_clause,[],[f1597,f1868])).

fof(f1597,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1846,plain,(
    ~ spl91_1 ),
    inference(avatar_split_clause,[],[f1156,f1843])).

fof(f1156,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f707])).

fof(f707,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f706])).

fof(f706,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f705])).

fof(f705,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
%------------------------------------------------------------------------------
