%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 173 expanded)
%              Number of leaves         :   21 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  259 ( 550 expanded)
%              Number of equality atoms :   43 (  85 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2443,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f73,f78,f88,f157,f1697,f1738,f1749,f1810,f1827,f1953,f2442])).

% (7579)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f2442,plain,
    ( ~ spl5_84
    | ~ spl5_2
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f2433,f1675,f69,f1950])).

fof(f1950,plain,
    ( spl5_84
  <=> r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f69,plain,
    ( spl5_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1675,plain,
    ( spl5_82
  <=> r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f2433,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ spl5_2
    | ~ spl5_82 ),
    inference(unit_resulting_resolution,[],[f1677,f1799])).

fof(f1799,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f70,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

% (7587)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f70,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f1677,plain,
    ( r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f1675])).

fof(f1953,plain,
    ( spl5_84
    | ~ spl5_3
    | spl5_16 ),
    inference(avatar_split_clause,[],[f1942,f188,f75,f1950])).

fof(f75,plain,
    ( spl5_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f188,plain,
    ( spl5_16
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1942,plain,
    ( r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ spl5_3
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f77,f190,f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1))),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f58,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f190,plain,
    ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f188])).

fof(f77,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f1827,plain,
    ( spl5_82
    | ~ spl5_3
    | spl5_16 ),
    inference(avatar_split_clause,[],[f1824,f188,f75,f1675])).

fof(f1824,plain,
    ( r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | ~ spl5_3
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f77,f190,f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1))),X1)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f57,f47])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1810,plain,
    ( ~ spl5_16
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1807,f75,f65,f188])).

fof(f65,plain,
    ( spl5_1
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1807,plain,
    ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0))
    | spl5_1
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f89,f67,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f67,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f89,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f77,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1749,plain,
    ( spl5_2
    | spl5_10 ),
    inference(avatar_split_clause,[],[f593,f127,f69])).

fof(f127,plain,
    ( spl5_10
  <=> r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f593,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f128,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f128,plain,
    ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f1738,plain,
    ( spl5_13
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f1737,f140,f127,f85,f75,f65,f154])).

fof(f154,plain,
    ( spl5_13
  <=> r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f85,plain,
    ( spl5_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f140,plain,
    ( spl5_12
  <=> r2_hidden(sK4(k1_relat_1(sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1737,plain,
    ( r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f1736,f87])).

fof(f87,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f1736,plain,
    ( r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_relat_1(k1_xboole_0))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f1729,f66])).

fof(f66,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f1729,plain,
    ( r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f77,f129,f142,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f142,plain,
    ( r2_hidden(sK4(k1_relat_1(sK1),sK0),sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f129,plain,
    ( r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f1697,plain,
    ( spl5_12
    | spl5_2 ),
    inference(avatar_split_clause,[],[f1693,f69,f140])).

fof(f1693,plain,
    ( r2_hidden(sK4(k1_relat_1(sK1),sK0),sK0)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f71,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f157,plain,
    ( ~ spl5_13
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f151,f140,f154])).

fof(f151,plain,
    ( ~ r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_xboole_0)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f142,f43,f54])).

fof(f43,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f88,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f41,f85])).

fof(f41,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f78,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f38,f75])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f73,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f39,f69,f65])).

fof(f39,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f40,f69,f65])).

fof(f40,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:39:38 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.44  % (7591)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.45  % (7584)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (7593)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (7583)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (7578)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (7584)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f2443,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f72,f73,f78,f88,f157,f1697,f1738,f1749,f1810,f1827,f1953,f2442])).
% 0.21/0.49  % (7579)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  fof(f2442,plain,(
% 0.21/0.49    ~spl5_84 | ~spl5_2 | ~spl5_82),
% 0.21/0.49    inference(avatar_split_clause,[],[f2433,f1675,f69,f1950])).
% 0.21/0.49  fof(f1950,plain,(
% 0.21/0.49    spl5_84 <=> r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl5_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f1675,plain,(
% 0.21/0.49    spl5_82 <=> r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).
% 0.21/0.49  fof(f2433,plain,(
% 0.21/0.49    ~r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | (~spl5_2 | ~spl5_82)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f1677,f1799])).
% 0.21/0.49  fof(f1799,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X1,sK0)) ) | ~spl5_2),
% 0.21/0.49    inference(resolution,[],[f70,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  % (7587)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f69])).
% 0.21/0.49  fof(f1677,plain,(
% 0.21/0.49    r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | ~spl5_82),
% 0.21/0.49    inference(avatar_component_clause,[],[f1675])).
% 0.21/0.49  fof(f1953,plain,(
% 0.21/0.49    spl5_84 | ~spl5_3 | spl5_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f1942,f188,f75,f1950])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl5_3 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    spl5_16 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.49  fof(f1942,plain,(
% 0.21/0.49    r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | (~spl5_3 | spl5_16)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f77,f190,f225])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1))),k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1))) )),
% 0.21/0.49    inference(resolution,[],[f58,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0)) | spl5_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f188])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    v1_relat_1(sK1) | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f1827,plain,(
% 0.21/0.49    spl5_82 | ~spl5_3 | spl5_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f1824,f188,f75,f1675])).
% 0.21/0.49  fof(f1824,plain,(
% 0.21/0.49    r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | (~spl5_3 | spl5_16)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f77,f190,f217])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK2(k1_relat_1(k7_relat_1(X0,X1))),X1) | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1))) )),
% 0.21/0.49    inference(resolution,[],[f57,f47])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f1810,plain,(
% 0.21/0.49    ~spl5_16 | spl5_1 | ~spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f1807,f75,f65,f188])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl5_1 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f1807,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0)) | (spl5_1 | ~spl5_3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f89,f67,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    k1_xboole_0 != k7_relat_1(sK1,sK0) | spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl5_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f77,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.49  fof(f1749,plain,(
% 0.21/0.49    spl5_2 | spl5_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f593,f127,f69])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl5_10 <=> r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.49  fof(f593,plain,(
% 0.21/0.49    r1_xboole_0(k1_relat_1(sK1),sK0) | spl5_10),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f128,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ~r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | spl5_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f127])).
% 0.21/0.49  fof(f1738,plain,(
% 0.21/0.49    spl5_13 | ~spl5_1 | ~spl5_3 | ~spl5_5 | ~spl5_10 | ~spl5_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f1737,f140,f127,f85,f75,f65,f154])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl5_13 <=> r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl5_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl5_12 <=> r2_hidden(sK4(k1_relat_1(sK1),sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.49  fof(f1737,plain,(
% 0.21/0.49    r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_xboole_0) | (~spl5_1 | ~spl5_3 | ~spl5_5 | ~spl5_10 | ~spl5_12)),
% 0.21/0.49    inference(forward_demodulation,[],[f1736,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f1736,plain,(
% 0.21/0.49    r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_relat_1(k1_xboole_0)) | (~spl5_1 | ~spl5_3 | ~spl5_10 | ~spl5_12)),
% 0.21/0.49    inference(forward_demodulation,[],[f1729,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f1729,plain,(
% 0.21/0.49    r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,sK0))) | (~spl5_3 | ~spl5_10 | ~spl5_12)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f77,f129,f142,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    r2_hidden(sK4(k1_relat_1(sK1),sK0),sK0) | ~spl5_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f140])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | ~spl5_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f127])).
% 0.21/0.49  fof(f1697,plain,(
% 0.21/0.49    spl5_12 | spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f1693,f69,f140])).
% 0.21/0.49  fof(f1693,plain,(
% 0.21/0.49    r2_hidden(sK4(k1_relat_1(sK1),sK0),sK0) | spl5_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f71,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f69])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ~spl5_13 | ~spl5_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f151,f140,f154])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ~r2_hidden(sK4(k1_relat_1(sK1),sK0),k1_xboole_0) | ~spl5_12),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f142,f43,f54])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl5_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f85])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f75])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f13])).
% 0.21/0.49  fof(f13,conjecture,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl5_1 | spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f69,f65])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~spl5_1 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f69,f65])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (7584)------------------------------
% 0.21/0.49  % (7584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7584)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (7584)Memory used [KB]: 7547
% 0.21/0.49  % (7584)Time elapsed: 0.074 s
% 0.21/0.49  % (7584)------------------------------
% 0.21/0.49  % (7584)------------------------------
% 0.21/0.49  % (7586)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (7574)Success in time 0.134 s
%------------------------------------------------------------------------------
