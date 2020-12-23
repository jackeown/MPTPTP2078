%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t23_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:11 EDT 2019

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 267 expanded)
%              Number of leaves         :   23 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  395 ( 789 expanded)
%              Number of equality atoms :   21 (  45 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2657,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f100,f113,f145,f179,f193,f211,f2114,f2126,f2309,f2318,f2629,f2653])).

fof(f2653,plain,
    ( ~ spl7_0
    | spl7_5
    | ~ spl7_234 ),
    inference(avatar_contradiction_clause,[],[f2652])).

fof(f2652,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_5
    | ~ spl7_234 ),
    inference(subsumption_resolution,[],[f2651,f112])).

fof(f112,plain,
    ( ~ v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl7_5
  <=> ~ v6_relat_2(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f2651,plain,
    ( v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl7_0
    | ~ spl7_234 ),
    inference(subsumption_resolution,[],[f2644,f103])).

fof(f103,plain,
    ( ! [X4] : v1_relat_1(k2_wellord1(sK1,X4))
    | ~ spl7_0 ),
    inference(resolution,[],[f92,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t23_wellord1.p',dt_k2_wellord1)).

fof(f92,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl7_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f2644,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl7_234 ),
    inference(resolution,[],[f2628,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t23_wellord1.p',l4_wellord1)).

fof(f2628,plain,
    ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ spl7_234 ),
    inference(avatar_component_clause,[],[f2627])).

fof(f2627,plain,
    ( spl7_234
  <=> r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_234])])).

fof(f2629,plain,
    ( spl7_234
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f2622,f950,f177,f143,f91,f2627])).

fof(f143,plain,
    ( spl7_6
  <=> r2_hidden(sK3(k2_wellord1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f177,plain,
    ( spl7_10
  <=> r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f950,plain,
    ( spl7_102
  <=> r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f2622,plain,
    ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f2618,f178])).

fof(f178,plain,
    ( r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f2618,plain,
    ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_102 ),
    inference(superposition,[],[f2556,f104])).

fof(f104,plain,
    ( ! [X5] : k2_wellord1(sK1,X5) = k3_xboole_0(sK1,k2_zfmisc_1(X5,X5))
    | ~ spl7_0 ),
    inference(resolution,[],[f92,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t23_wellord1.p',d6_wellord1)).

fof(f2556,plain,
    ( ! [X2] :
        ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,X2)))
        | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X2) )
    | ~ spl7_6
    | ~ spl7_102 ),
    inference(forward_demodulation,[],[f2555,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t23_wellord1.p',commutativity_k3_xboole_0)).

fof(f2555,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X2)
        | r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k3_xboole_0(k2_zfmisc_1(sK0,X2),sK1)) )
    | ~ spl7_6
    | ~ spl7_102 ),
    inference(resolution,[],[f2323,f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t23_wellord1.p',d4_xboole_0)).

fof(f2323,plain,
    ( ! [X1] :
        ( sP6(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1,k2_zfmisc_1(sK0,X1))
        | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X1) )
    | ~ spl7_6
    | ~ spl7_102 ),
    inference(resolution,[],[f951,f257])).

fof(f257,plain,
    ( ! [X10,X8,X9] :
        ( ~ r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),X8),X10)
        | ~ r2_hidden(X8,X9)
        | sP6(k4_tarski(sK3(k2_wellord1(sK1,sK0)),X8),X10,k2_zfmisc_1(sK0,X9)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f149,f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),X0),k2_zfmisc_1(sK0,X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f144,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t23_wellord1.p',t106_zfmisc_1)).

fof(f144,plain,
    ( r2_hidden(sK3(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f143])).

fof(f951,plain,
    ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1)
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f950])).

fof(f2318,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_16
    | spl7_95
    | spl7_97
    | spl7_103 ),
    inference(avatar_contradiction_clause,[],[f2317])).

fof(f2317,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_95
    | ~ spl7_97
    | ~ spl7_103 ),
    inference(subsumption_resolution,[],[f2316,f948])).

fof(f948,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1)
    | ~ spl7_103 ),
    inference(avatar_component_clause,[],[f947])).

fof(f947,plain,
    ( spl7_103
  <=> ~ r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f2316,plain,
    ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_95
    | ~ spl7_97 ),
    inference(subsumption_resolution,[],[f2315,f192])).

fof(f192,plain,
    ( r2_hidden(sK3(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl7_12
  <=> r2_hidden(sK3(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f2315,plain,
    ( ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_16
    | ~ spl7_95
    | ~ spl7_97 ),
    inference(subsumption_resolution,[],[f2314,f921])).

fof(f921,plain,
    ( sK2(k2_wellord1(sK1,sK0)) != sK3(k2_wellord1(sK1,sK0))
    | ~ spl7_97 ),
    inference(avatar_component_clause,[],[f920])).

fof(f920,plain,
    ( spl7_97
  <=> sK2(k2_wellord1(sK1,sK0)) != sK3(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f2314,plain,
    ( sK2(k2_wellord1(sK1,sK0)) = sK3(k2_wellord1(sK1,sK0))
    | ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_16
    | ~ spl7_95 ),
    inference(resolution,[],[f915,f212])).

fof(f212,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),X0),sK1)
        | sK2(k2_wellord1(sK1,sK0)) = X0
        | ~ r2_hidden(X0,k3_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,sK2(k2_wellord1(sK1,sK0))),sK1) )
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_16 ),
    inference(resolution,[],[f210,f106])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK1))
        | ~ r2_hidden(X1,k3_relat_1(sK1))
        | X0 = X1
        | r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f105,f92])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK1))
        | ~ r2_hidden(X1,k3_relat_1(sK1))
        | X0 = X1
        | r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_2 ),
    inference(resolution,[],[f99,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_relat_2(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f99,plain,
    ( v6_relat_2(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_2
  <=> v6_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f210,plain,
    ( r2_hidden(sK2(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl7_16
  <=> r2_hidden(sK2(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f915,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),sK1)
    | ~ spl7_95 ),
    inference(avatar_component_clause,[],[f914])).

fof(f914,plain,
    ( spl7_95
  <=> ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f2309,plain,
    ( ~ spl7_0
    | spl7_5
    | ~ spl7_96 ),
    inference(avatar_contradiction_clause,[],[f2308])).

fof(f2308,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_5
    | ~ spl7_96 ),
    inference(subsumption_resolution,[],[f2307,f112])).

fof(f2307,plain,
    ( v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl7_0
    | ~ spl7_96 ),
    inference(subsumption_resolution,[],[f2265,f103])).

fof(f2265,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl7_96 ),
    inference(trivial_inequality_removal,[],[f2262])).

fof(f2262,plain,
    ( sK2(k2_wellord1(sK1,sK0)) != sK2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl7_96 ),
    inference(superposition,[],[f58,f924])).

fof(f924,plain,
    ( sK2(k2_wellord1(sK1,sK0)) = sK3(k2_wellord1(sK1,sK0))
    | ~ spl7_96 ),
    inference(avatar_component_clause,[],[f923])).

fof(f923,plain,
    ( spl7_96
  <=> sK2(k2_wellord1(sK1,sK0)) = sK3(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f58,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2126,plain,
    ( ~ spl7_0
    | spl7_5
    | ~ spl7_226 ),
    inference(avatar_contradiction_clause,[],[f2125])).

fof(f2125,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_5
    | ~ spl7_226 ),
    inference(subsumption_resolution,[],[f2124,f112])).

fof(f2124,plain,
    ( v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl7_0
    | ~ spl7_226 ),
    inference(subsumption_resolution,[],[f2117,f103])).

fof(f2117,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl7_226 ),
    inference(resolution,[],[f2113,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2113,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ spl7_226 ),
    inference(avatar_component_clause,[],[f2112])).

fof(f2112,plain,
    ( spl7_226
  <=> r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_226])])).

fof(f2114,plain,
    ( spl7_226
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_94 ),
    inference(avatar_split_clause,[],[f2107,f917,f177,f143,f91,f2112])).

fof(f917,plain,
    ( spl7_94
  <=> r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f2107,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ spl7_0
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_94 ),
    inference(subsumption_resolution,[],[f2103,f144])).

fof(f2103,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl7_0
    | ~ spl7_10
    | ~ spl7_94 ),
    inference(superposition,[],[f1171,f104])).

fof(f1171,plain,
    ( ! [X2] :
        ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,X2)))
        | ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),X2) )
    | ~ spl7_10
    | ~ spl7_94 ),
    inference(forward_demodulation,[],[f1170,f66])).

fof(f1170,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),X2)
        | r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k3_xboole_0(k2_zfmisc_1(sK0,X2),sK1)) )
    | ~ spl7_10
    | ~ spl7_94 ),
    inference(resolution,[],[f928,f86])).

fof(f928,plain,
    ( ! [X1] :
        ( sP6(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),sK1,k2_zfmisc_1(sK0,X1))
        | ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),X1) )
    | ~ spl7_10
    | ~ spl7_94 ),
    inference(resolution,[],[f918,f269])).

fof(f269,plain,
    ( ! [X10,X8,X9] :
        ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),X8),X10)
        | ~ r2_hidden(X8,X9)
        | sP6(k4_tarski(sK2(k2_wellord1(sK1,sK0)),X8),X10,k2_zfmisc_1(sK0,X9)) )
    | ~ spl7_10 ),
    inference(resolution,[],[f184,f75])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),X0),k2_zfmisc_1(sK0,X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_10 ),
    inference(resolution,[],[f178,f84])).

fof(f918,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),sK1)
    | ~ spl7_94 ),
    inference(avatar_component_clause,[],[f917])).

fof(f211,plain,
    ( spl7_16
    | ~ spl7_0
    | spl7_5 ),
    inference(avatar_split_clause,[],[f166,f111,f91,f209])).

fof(f166,plain,
    ( r2_hidden(sK2(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | ~ spl7_0
    | ~ spl7_5 ),
    inference(resolution,[],[f133,f112])).

fof(f133,plain,
    ( ! [X1] :
        ( v6_relat_2(k2_wellord1(sK1,X1))
        | r2_hidden(sK2(k2_wellord1(sK1,X1)),k3_relat_1(sK1)) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f131,f103])).

fof(f131,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(k2_wellord1(sK1,X1)),k3_relat_1(sK1))
        | ~ v1_relat_1(k2_wellord1(sK1,X1))
        | v6_relat_2(k2_wellord1(sK1,X1)) )
    | ~ spl7_0 ),
    inference(resolution,[],[f101,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(sK1,X1)))
        | r2_hidden(X0,k3_relat_1(sK1)) )
    | ~ spl7_0 ),
    inference(resolution,[],[f92,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t23_wellord1.p',t19_wellord1)).

fof(f193,plain,
    ( spl7_12
    | ~ spl7_0
    | spl7_5 ),
    inference(avatar_split_clause,[],[f156,f111,f91,f191])).

fof(f156,plain,
    ( r2_hidden(sK3(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | ~ spl7_0
    | ~ spl7_5 ),
    inference(resolution,[],[f132,f112])).

fof(f132,plain,
    ( ! [X0] :
        ( v6_relat_2(k2_wellord1(sK1,X0))
        | r2_hidden(sK3(k2_wellord1(sK1,X0)),k3_relat_1(sK1)) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f130,f103])).

fof(f130,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k2_wellord1(sK1,X0)),k3_relat_1(sK1))
        | ~ v1_relat_1(k2_wellord1(sK1,X0))
        | v6_relat_2(k2_wellord1(sK1,X0)) )
    | ~ spl7_0 ),
    inference(resolution,[],[f101,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f179,plain,
    ( spl7_10
    | ~ spl7_0
    | spl7_5 ),
    inference(avatar_split_clause,[],[f146,f111,f91,f177])).

fof(f146,plain,
    ( r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl7_0
    | ~ spl7_5 ),
    inference(resolution,[],[f125,f112])).

fof(f125,plain,
    ( ! [X1] :
        ( v6_relat_2(k2_wellord1(sK1,X1))
        | r2_hidden(sK2(k2_wellord1(sK1,X1)),X1) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f123,f103])).

fof(f123,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(k2_wellord1(sK1,X1)),X1)
        | ~ v1_relat_1(k2_wellord1(sK1,X1))
        | v6_relat_2(k2_wellord1(sK1,X1)) )
    | ~ spl7_0 ),
    inference(resolution,[],[f102,f56])).

fof(f102,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k3_relat_1(k2_wellord1(sK1,X3)))
        | r2_hidden(X2,X3) )
    | ~ spl7_0 ),
    inference(resolution,[],[f92,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f145,plain,
    ( spl7_6
    | ~ spl7_0
    | spl7_5 ),
    inference(avatar_split_clause,[],[f134,f111,f91,f143])).

fof(f134,plain,
    ( r2_hidden(sK3(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl7_0
    | ~ spl7_5 ),
    inference(resolution,[],[f124,f112])).

fof(f124,plain,
    ( ! [X0] :
        ( v6_relat_2(k2_wellord1(sK1,X0))
        | r2_hidden(sK3(k2_wellord1(sK1,X0)),X0) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f122,f103])).

fof(f122,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k2_wellord1(sK1,X0)),X0)
        | ~ v1_relat_1(k2_wellord1(sK1,X0))
        | v6_relat_2(k2_wellord1(sK1,X0)) )
    | ~ spl7_0 ),
    inference(resolution,[],[f102,f57])).

fof(f113,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f50,f111])).

fof(f50,plain,(
    ~ v6_relat_2(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ~ v6_relat_2(k2_wellord1(X1,X0))
      & v6_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ~ v6_relat_2(k2_wellord1(X1,X0))
      & v6_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v6_relat_2(X1)
         => v6_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
       => v6_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t23_wellord1.p',t23_wellord1)).

fof(f100,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    v6_relat_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
