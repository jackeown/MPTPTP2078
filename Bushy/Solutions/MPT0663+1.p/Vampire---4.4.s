%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t71_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:27 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 101 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 267 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f79,f86,f93,f100,f109,f117,f125,f132,f170])).

fof(f170,plain,
    ( ~ spl4_0
    | ~ spl4_2
    | ~ spl4_10
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f163,f131])).

fof(f131,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl4_17
  <=> k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f163,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(resolution,[],[f159,f108])).

fof(f108,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_10
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f159,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k3_xboole_0(X2,k1_relat_1(sK2)))
        | k1_funct_1(sK2,X3) = k1_funct_1(k7_relat_1(sK2,X2),X3) )
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(superposition,[],[f154,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t71_funct_1.p',commutativity_k3_xboole_0)).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),X1))
        | k1_funct_1(sK2,X0) = k1_funct_1(k7_relat_1(sK2,X1),X0) )
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f153,f146])).

fof(f146,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl4_0 ),
    inference(resolution,[],[f56,f71])).

fof(f71,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t71_funct_1.p',t90_relat_1)).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
        | k1_funct_1(sK2,X0) = k1_funct_1(k7_relat_1(sK2,X1),X0) )
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f151,f71])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
        | k1_funct_1(sK2,X0) = k1_funct_1(k7_relat_1(sK2,X1),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f64,f78])).

fof(f78,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t71_funct_1.p',t70_funct_1)).

fof(f132,plain,(
    ~ spl4_17 ),
    inference(avatar_split_clause,[],[f47,f130])).

fof(f47,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
      & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t71_funct_1.p',t71_funct_1)).

fof(f125,plain,
    ( ~ spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f118,f107,f123])).

fof(f123,plain,
    ( spl4_15
  <=> ~ r2_hidden(k3_xboole_0(sK1,k1_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f118,plain,
    ( ~ r2_hidden(k3_xboole_0(sK1,k1_relat_1(sK2)),sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f58,f108])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t71_funct_1.p',antisymmetry_r2_hidden)).

fof(f117,plain,
    ( ~ spl4_13
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f110,f107,f115])).

fof(f115,plain,
    ( spl4_13
  <=> ~ v1_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f110,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)))
    | ~ spl4_10 ),
    inference(resolution,[],[f108,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t71_funct_1.p',t7_boole)).

fof(f109,plain,
    ( spl4_10
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f101,f98,f107])).

fof(f98,plain,
    ( spl4_8
  <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f101,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2)))
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f99,f54])).

fof(f99,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f46,f98])).

fof(f46,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f49,f91])).

fof(f91,plain,
    ( spl4_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f49,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_1__t71_funct_1.p',d2_xboole_0)).

fof(f86,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f65,f84])).

fof(f84,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f48,f49])).

fof(f48,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t71_funct_1.p',dt_o_0_0_xboole_0)).

fof(f79,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f45,f77])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f44,f70])).

fof(f44,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
