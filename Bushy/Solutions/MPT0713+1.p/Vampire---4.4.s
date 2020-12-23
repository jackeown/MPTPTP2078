%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t168_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:19 EDT 2019

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 404 expanded)
%              Number of leaves         :   38 ( 149 expanded)
%              Depth                    :   12
%              Number of atoms          :  580 (1242 expanded)
%              Number of equality atoms :   55 ( 163 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f109,f116,f123,f132,f145,f164,f186,f268,f292,f348,f428,f529,f588,f747,f858,f882,f887,f889,f893,f908,f985,f1037,f1069,f1285,f1357])).

fof(f1357,plain,
    ( ~ spl7_0
    | ~ spl7_4
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f1356])).

fof(f1356,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f1355,f101])).

fof(f101,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f1355,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_4
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f1354,f115])).

fof(f115,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl7_4
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1354,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f1353,f89])).

fof(f89,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t168_funct_1.p',d1_tarski)).

fof(f1353,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_45 ),
    inference(resolution,[],[f1284,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t168_funct_1.p',t86_relat_1)).

fof(f1284,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f1283])).

fof(f1283,plain,
    ( spl7_45
  <=> ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f1285,plain,
    ( ~ spl7_35
    | ~ spl7_45
    | ~ spl7_39
    | spl7_21
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f688,f586,f346,f880,f1283,f871])).

fof(f871,plain,
    ( spl7_35
  <=> ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f880,plain,
    ( spl7_39
  <=> ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f346,plain,
    ( spl7_21
  <=> ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f586,plain,
    ( spl7_26
  <=> k1_funct_1(sK1,sK0) = k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f688,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl7_21
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f684,f347])).

fof(f347,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f346])).

fof(f684,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl7_26 ),
    inference(superposition,[],[f93,f587])).

fof(f587,plain,
    ( k1_funct_1(sK1,sK0) = k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f586])).

fof(f93,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t168_funct_1.p',d5_funct_1)).

fof(f1069,plain,
    ( spl7_42
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f458,f426,f107,f100,f1067])).

fof(f1067,plain,
    ( spl7_42
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK4(sK1,k1_funct_1(sK1,sK0))))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f107,plain,
    ( spl7_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f426,plain,
    ( spl7_22
  <=> k1_funct_1(sK1,sK0) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f458,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK4(sK1,k1_funct_1(sK1,sK0))))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f457,f101])).

fof(f457,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK4(sK1,k1_funct_1(sK1,sK0))))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f447,f108])).

fof(f108,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f447,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK4(sK1,k1_funct_1(sK1,sK0))))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_22 ),
    inference(superposition,[],[f71,f427])).

fof(f427,plain,
    ( k1_funct_1(sK1,sK0) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,sK0)))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f426])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t168_funct_1.p',t167_funct_1)).

fof(f1037,plain,
    ( ~ spl7_29
    | spl7_32
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f456,f426,f107,f100,f853,f739])).

fof(f739,plain,
    ( spl7_29
  <=> ~ r2_hidden(sK4(sK1,k1_funct_1(sK1,sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f853,plain,
    ( spl7_32
  <=> r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f456,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ r2_hidden(sK4(sK1,k1_funct_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f455,f101])).

fof(f455,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ r2_hidden(sK4(sK1,k1_funct_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f446,f108])).

fof(f446,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK4(sK1,k1_funct_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_22 ),
    inference(superposition,[],[f93,f427])).

fof(f985,plain,
    ( ~ spl7_41
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f953,f736,f983])).

fof(f983,plain,
    ( spl7_41
  <=> ~ r2_hidden(k1_relat_1(sK1),sK4(sK1,k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f736,plain,
    ( spl7_28
  <=> r2_hidden(sK4(sK1,k1_funct_1(sK1,sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f953,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK4(sK1,k1_funct_1(sK1,sK0)))
    | ~ spl7_28 ),
    inference(resolution,[],[f737,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t168_funct_1.p',antisymmetry_r2_hidden)).

fof(f737,plain,
    ( r2_hidden(sK4(sK1,k1_funct_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f736])).

fof(f908,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | spl7_33 ),
    inference(avatar_contradiction_clause,[],[f907])).

fof(f907,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f906,f101])).

fof(f906,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f905,f115])).

fof(f905,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f904,f108])).

fof(f904,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_33 ),
    inference(resolution,[],[f857,f93])).

fof(f857,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f856])).

fof(f856,plain,
    ( spl7_33
  <=> ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f893,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | spl7_39 ),
    inference(avatar_contradiction_clause,[],[f892])).

fof(f892,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f891,f101])).

fof(f891,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f890,f108])).

fof(f890,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_39 ),
    inference(resolution,[],[f881,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t168_funct_1.p',fc8_funct_1)).

fof(f881,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f880])).

fof(f889,plain,
    ( ~ spl7_0
    | spl7_35 ),
    inference(avatar_contradiction_clause,[],[f888])).

fof(f888,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f884,f101])).

fof(f884,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_35 ),
    inference(resolution,[],[f872,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t168_funct_1.p',dt_k7_relat_1)).

fof(f872,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f871])).

fof(f887,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | spl7_35 ),
    inference(avatar_contradiction_clause,[],[f886])).

fof(f886,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f885,f101])).

fof(f885,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f883,f108])).

fof(f883,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_35 ),
    inference(resolution,[],[f872,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f882,plain,
    ( ~ spl7_35
    | spl7_36
    | ~ spl7_39
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f191,f159,f880,f874,f871])).

fof(f874,plain,
    ( spl7_36
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | r2_hidden(k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),X0),k1_tarski(k1_funct_1(sK1,sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f159,plain,
    ( spl7_14
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
        | r2_hidden(k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),X0),k1_tarski(k1_funct_1(sK1,sK0))) )
    | ~ spl7_14 ),
    inference(resolution,[],[f93,f187])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
        | r2_hidden(X0,k1_tarski(k1_funct_1(sK1,sK0))) )
    | ~ spl7_14 ),
    inference(resolution,[],[f160,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t168_funct_1.p',d3_tarski)).

fof(f160,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f858,plain,
    ( ~ spl7_33
    | ~ spl7_0
    | ~ spl7_2
    | spl7_29 ),
    inference(avatar_split_clause,[],[f815,f739,f107,f100,f856])).

fof(f815,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f814,f101])).

fof(f814,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ spl7_2
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f813,f108])).

fof(f813,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ spl7_29 ),
    inference(resolution,[],[f740,f95])).

fof(f95,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f740,plain,
    ( ~ r2_hidden(sK4(sK1,k1_funct_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f739])).

fof(f747,plain,
    ( ~ spl7_29
    | ~ spl7_31
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f449,f426,f107,f100,f745,f739])).

fof(f745,plain,
    ( spl7_31
  <=> ~ r2_hidden(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f449,plain,
    ( ~ r2_hidden(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK4(sK1,k1_funct_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f448,f108])).

fof(f448,plain,
    ( ~ r2_hidden(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK4(sK1,k1_funct_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ spl7_0
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f443,f101])).

fof(f443,plain,
    ( ~ r2_hidden(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK4(sK1,k1_funct_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl7_22 ),
    inference(superposition,[],[f192,f427])).

fof(f192,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k2_relat_1(X1),k1_funct_1(X1,X2))
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f93,f86])).

fof(f588,plain,
    ( spl7_26
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f500,f114,f107,f100,f586])).

fof(f500,plain,
    ( k1_funct_1(sK1,sK0) = k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f480,f89])).

fof(f480,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK0,X4)
        | k1_funct_1(sK1,sK0) = k1_funct_1(k7_relat_1(sK1,X4),sK0) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f479,f108])).

fof(f479,plain,
    ( ! [X4] :
        ( k1_funct_1(sK1,sK0) = k1_funct_1(k7_relat_1(sK1,X4),sK0)
        | ~ r2_hidden(sK0,X4)
        | ~ v1_funct_1(sK1) )
    | ~ spl7_0
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f460,f101])).

fof(f460,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(sK1)
        | k1_funct_1(sK1,sK0) = k1_funct_1(k7_relat_1(sK1,X4),sK0)
        | ~ r2_hidden(sK0,X4)
        | ~ v1_funct_1(sK1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f222,f115])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,X1) = k1_funct_1(k7_relat_1(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,X1) = k1_funct_1(k7_relat_1(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f56,f74])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t168_funct_1.p',t70_funct_1)).

fof(f529,plain,
    ( spl7_24
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f499,f114,f107,f100,f527])).

fof(f527,plain,
    ( spl7_24
  <=> k1_funct_1(sK1,sK0) = k1_funct_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f499,plain,
    ( k1_funct_1(sK1,sK0) = k1_funct_1(k7_relat_1(sK1,k1_relat_1(sK1)),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f480,f115])).

fof(f428,plain,
    ( spl7_22
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f421,f114,f107,f100,f426])).

fof(f421,plain,
    ( k1_funct_1(sK1,sK0) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,sK0)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f420,f108])).

fof(f420,plain,
    ( k1_funct_1(sK1,sK0) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl7_0
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f403,f101])).

fof(f403,plain,
    ( k1_funct_1(sK1,sK0) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl7_4 ),
    inference(resolution,[],[f217,f115])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = k1_funct_1(X0,sK4(X0,k1_funct_1(X0,X1)))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,X1) = k1_funct_1(X0,sK4(X0,k1_funct_1(X0,X1)))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f94,f93])).

fof(f94,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f348,plain,
    ( ~ spl7_21
    | spl7_13
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f304,f266,f156,f346])).

fof(f156,plain,
    ( spl7_13
  <=> ~ r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f266,plain,
    ( spl7_16
  <=> k1_funct_1(sK1,sK0) = sK6(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f304,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f302,f157])).

fof(f157,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f156])).

fof(f302,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_16 ),
    inference(superposition,[],[f83,f267])).

fof(f267,plain,
    ( k1_funct_1(sK1,sK0) = sK6(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f266])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f292,plain,
    ( ~ spl7_19
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f285,f114,f107,f100,f290])).

fof(f290,plain,
    ( spl7_19
  <=> ~ v1_xboole_0(k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f285,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f284,f101])).

fof(f284,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_xboole_0(k2_relat_1(sK1))
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f274,f108])).

fof(f274,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_xboole_0(k2_relat_1(sK1))
    | ~ spl7_4 ),
    inference(resolution,[],[f193,f115])).

fof(f193,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_xboole_0(k2_relat_1(X3)) ) ),
    inference(resolution,[],[f93,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t168_funct_1.p',t7_boole)).

fof(f268,plain,
    ( spl7_16
    | spl7_13 ),
    inference(avatar_split_clause,[],[f259,f156,f266])).

fof(f259,plain,
    ( k1_funct_1(sK1,sK0) = sK6(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_13 ),
    inference(resolution,[],[f138,f157])).

fof(f138,plain,(
    ! [X4,X5] :
      ( r1_tarski(k1_tarski(X4),X5)
      | sK6(k1_tarski(X4),X5) = X4 ) ),
    inference(resolution,[],[f82,f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f186,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f184,f101])).

fof(f184,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_2
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f181,f108])).

fof(f181,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_15 ),
    inference(resolution,[],[f71,f163])).

fof(f163,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl7_15
  <=> ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f164,plain,
    ( ~ spl7_13
    | ~ spl7_15
    | spl7_7 ),
    inference(avatar_split_clause,[],[f149,f121,f162,f156])).

fof(f121,plain,
    ( spl7_7
  <=> k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f149,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_7 ),
    inference(extensionality_resolution,[],[f64,f122])).

fof(f122,plain,
    ( k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t168_funct_1.p',d10_xboole_0)).

fof(f145,plain,
    ( ~ spl7_11
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f133,f114,f143])).

fof(f143,plain,
    ( spl7_11
  <=> ~ r2_hidden(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f133,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f115])).

fof(f132,plain,
    ( ~ spl7_9
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f124,f114,f130])).

fof(f130,plain,
    ( spl7_9
  <=> ~ v1_xboole_0(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f124,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl7_4 ),
    inference(resolution,[],[f80,f115])).

fof(f123,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f55,f121])).

fof(f55,plain,(
    k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t168_funct_1.p',t168_funct_1)).

fof(f116,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f54,f114])).

fof(f54,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f109,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f53,f107])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f52,f100])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
