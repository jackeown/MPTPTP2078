%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0549+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:10 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 208 expanded)
%              Number of leaves         :   30 (  95 expanded)
%              Depth                    :    8
%              Number of atoms          :  377 ( 633 expanded)
%              Number of equality atoms :   35 (  57 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f659,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f45,f48,f52,f56,f60,f64,f68,f72,f76,f92,f96,f100,f107,f123,f149,f153,f167,f187,f233,f267,f314,f333,f548,f649,f658])).

fof(f658,plain,
    ( spl7_2
    | ~ spl7_5
    | ~ spl7_67 ),
    inference(avatar_contradiction_clause,[],[f657])).

fof(f657,plain,
    ( $false
    | spl7_2
    | ~ spl7_5
    | ~ spl7_67 ),
    inference(subsumption_resolution,[],[f651,f46])).

fof(f46,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl7_2
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f651,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl7_5
    | ~ spl7_67 ),
    inference(superposition,[],[f55,f648])).

fof(f648,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k9_relat_1(sK1,sK0),X2)
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f647])).

fof(f647,plain,
    ( spl7_67
  <=> ! [X2] : k1_xboole_0 = k3_xboole_0(k9_relat_1(sK1,sK0),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f55,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl7_5
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f649,plain,
    ( spl7_67
    | ~ spl7_9
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f511,f331,f70,f647])).

fof(f70,plain,
    ( spl7_9
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f331,plain,
    ( spl7_45
  <=> ! [X4] : r1_xboole_0(k9_relat_1(sK1,sK0),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f511,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k9_relat_1(sK1,sK0),X2)
    | ~ spl7_9
    | ~ spl7_45 ),
    inference(resolution,[],[f332,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f332,plain,
    ( ! [X4] : r1_xboole_0(k9_relat_1(sK1,sK0),X4)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f331])).

fof(f548,plain,
    ( spl7_14
    | ~ spl7_13
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f546,f231,f90,f94])).

fof(f94,plain,
    ( spl7_14
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f90,plain,
    ( spl7_13
  <=> ! [X0,X2] :
        ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
        | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f231,plain,
    ( spl7_33
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f546,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X2,k1_relat_1(sK1)) )
    | ~ spl7_13
    | ~ spl7_33 ),
    inference(resolution,[],[f232,f91])).

fof(f91,plain,
    ( ! [X2,X0] :
        ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
        | ~ r2_hidden(X2,k1_relat_1(X0)) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f231])).

fof(f333,plain,
    ( spl7_45
    | ~ spl7_6
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f321,f312,f58,f331])).

fof(f58,plain,
    ( spl7_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f312,plain,
    ( spl7_43
  <=> ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f321,plain,
    ( ! [X4] : r1_xboole_0(k9_relat_1(sK1,sK0),X4)
    | ~ spl7_6
    | ~ spl7_43 ),
    inference(resolution,[],[f313,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f313,plain,
    ( ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f312])).

fof(f314,plain,
    ( spl7_43
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f277,f265,f105,f36,f312])).

fof(f36,plain,
    ( spl7_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f105,plain,
    ( spl7_16
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f265,plain,
    ( spl7_36
  <=> ! [X4] :
        ( ~ r2_hidden(sK6(X4,sK0,sK1),k1_relat_1(sK1))
        | ~ r2_hidden(X4,k9_relat_1(sK1,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f277,plain,
    ( ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f276,f37])).

fof(f37,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1) )
    | ~ spl7_16
    | ~ spl7_36 ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k9_relat_1(sK1,sK0)) )
    | ~ spl7_16
    | ~ spl7_36 ),
    inference(resolution,[],[f266,f106])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f266,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK6(X4,sK0,sK1),k1_relat_1(sK1))
        | ~ r2_hidden(X4,k9_relat_1(sK1,sK0)) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f265])).

fof(f267,plain,
    ( spl7_36
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f250,f151,f94,f265])).

fof(f151,plain,
    ( spl7_25
  <=> ! [X1,X0] :
        ( r2_hidden(sK6(X0,X1,sK1),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f250,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK6(X4,sK0,sK1),k1_relat_1(sK1))
        | ~ r2_hidden(X4,k9_relat_1(sK1,sK0)) )
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(resolution,[],[f95,f152])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(X0,X1,sK1),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f151])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f233,plain,
    ( spl7_33
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_19
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f227,f185,f121,f50,f40,f36,f231])).

fof(f50,plain,
    ( spl7_4
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f121,plain,
    ( spl7_19
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(X3,X0),X2)
        | ~ r2_hidden(X3,X1)
        | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f185,plain,
    ( spl7_28
  <=> ! [X1,X3,X2] :
        ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X1,X3)
        | k1_xboole_0 != k3_xboole_0(X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_19
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f226,f37])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ r2_hidden(X1,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_19
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f225,f196])).

fof(f196,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_28 ),
    inference(condensation,[],[f195])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl7_4
    | ~ spl7_28 ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl7_4
    | ~ spl7_28 ),
    inference(superposition,[],[f186,f51])).

fof(f51,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f186,plain,
    ( ! [X2,X3,X1] :
        ( k1_xboole_0 != k3_xboole_0(X3,X2)
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X1,X2) )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f185])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ r2_hidden(X1,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(superposition,[],[f122,f41])).

fof(f41,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f122,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ r2_hidden(k4_tarski(X3,X0),X2)
        | ~ r2_hidden(X3,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f121])).

fof(f187,plain,
    ( spl7_28
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f84,f74,f66,f185])).

fof(f66,plain,
    ( spl7_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f74,plain,
    ( spl7_10
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f84,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X1,X3)
        | k1_xboole_0 != k3_xboole_0(X3,X2) )
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(resolution,[],[f75,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f167,plain,
    ( spl7_3
    | ~ spl7_6
    | ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl7_3
    | ~ spl7_6
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f47,f156])).

fof(f156,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl7_6
    | ~ spl7_24 ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl7_6
    | ~ spl7_24 ),
    inference(resolution,[],[f148,f59])).

fof(f148,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(X1,sK0),k1_relat_1(sK1))
        | r1_xboole_0(X1,sK0) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl7_24
  <=> ! [X1] :
        ( ~ r2_hidden(sK2(X1,sK0),k1_relat_1(sK1))
        | r1_xboole_0(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f47,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl7_3
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f153,plain,
    ( spl7_25
    | ~ spl7_1
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f108,f98,f36,f151])).

fof(f98,plain,
    ( spl7_15
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(sK6(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(X0,X1,sK1),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) )
    | ~ spl7_1
    | ~ spl7_15 ),
    inference(resolution,[],[f99,f37])).

fof(f99,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(sK6(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f98])).

fof(f149,plain,
    ( spl7_24
    | ~ spl7_7
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f102,f94,f62,f147])).

fof(f62,plain,
    ( spl7_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK2(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f102,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(X1,sK0),k1_relat_1(sK1))
        | r1_xboole_0(X1,sK0) )
    | ~ spl7_7
    | ~ spl7_14 ),
    inference(resolution,[],[f95,f63])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f123,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f34,f121])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f31,f33])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f107,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f28,f105])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f100,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f30,f98])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f96,plain,
    ( spl7_14
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f83,f74,f43,f94])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(resolution,[],[f75,f44])).

fof(f44,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f92,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f32,f90])).

fof(f32,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f76,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f19,f74])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f72,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f23,f70])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f68,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f22,f66])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f64,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f21,f62])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f20,f58])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f18,f54])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f52,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f17,f50])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f48,plain,
    ( ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f15,f43,f40])).

fof(f15,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

% (13533)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f45,plain,
    ( spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f14,f43,f40])).

fof(f14,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
