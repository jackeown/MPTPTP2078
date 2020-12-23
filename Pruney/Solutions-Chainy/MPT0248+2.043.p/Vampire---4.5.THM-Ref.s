%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:55 EST 2020

% Result     : Theorem 2.69s
% Output     : Refutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 254 expanded)
%              Number of leaves         :   39 ( 102 expanded)
%              Depth                    :    9
%              Number of atoms          :  338 ( 654 expanded)
%              Number of equality atoms :  111 ( 285 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2510,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f98,f99,f104,f303,f536,f1646,f1672,f2076,f2084,f2090,f2121,f2149,f2150,f2167,f2471,f2494,f2496,f2508])).

fof(f2508,plain,
    ( ~ spl5_16
    | spl5_20 ),
    inference(avatar_split_clause,[],[f583,f382,f300])).

fof(f300,plain,
    ( spl5_16
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f382,plain,
    ( spl5_20
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f583,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_20 ),
    inference(resolution,[],[f383,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f114,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f114,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f76,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f383,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f382])).

fof(f2496,plain,
    ( spl5_16
    | ~ spl5_43
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f2457,f110,f2461,f300])).

fof(f2461,plain,
    ( spl5_43
  <=> r1_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f110,plain,
    ( spl5_6
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f2457,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | v1_xboole_0(sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f458,f112])).

fof(f112,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f458,plain,(
    ! [X26,X25] :
      ( ~ r1_tarski(X26,X25)
      | ~ r1_xboole_0(X25,X26)
      | v1_xboole_0(X26) ) ),
    inference(superposition,[],[f159,f136])).

fof(f136,plain,(
    ! [X4,X3] :
      ( k3_xboole_0(X4,X3) = X3
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f61,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f159,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f75,f72])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f2494,plain,
    ( ~ spl5_7
    | spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f390,f101,f95,f147])).

fof(f147,plain,
    ( spl5_7
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f95,plain,
    ( spl5_4
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f101,plain,
    ( spl5_5
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f390,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_5 ),
    inference(superposition,[],[f103,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f103,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f2471,plain,
    ( spl5_13
    | spl5_43 ),
    inference(avatar_contradiction_clause,[],[f2470])).

fof(f2470,plain,
    ( $false
    | spl5_13
    | spl5_43 ),
    inference(subsumption_resolution,[],[f2466,f200])).

fof(f200,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl5_13
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f2466,plain,
    ( r2_hidden(sK0,sK1)
    | spl5_43 ),
    inference(resolution,[],[f2463,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f2463,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | spl5_43 ),
    inference(avatar_component_clause,[],[f2461])).

fof(f2167,plain,
    ( ~ spl5_35
    | spl5_36
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f2164,f1669,f2059,f2055])).

fof(f2055,plain,
    ( spl5_35
  <=> v1_xboole_0(k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f2059,plain,
    ( spl5_36
  <=> sK1 = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f1669,plain,
    ( spl5_32
  <=> k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f2164,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | ~ v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ spl5_32 ),
    inference(superposition,[],[f288,f1671])).

fof(f1671,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f1669])).

fof(f288,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f207,f52])).

fof(f207,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f202,f53])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f202,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f73,f55])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f2150,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f2139,f101,f110])).

fof(f2139,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl5_5 ),
    inference(superposition,[],[f67,f103])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2149,plain,
    ( spl5_14
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f2137,f101,f271])).

fof(f271,plain,
    ( spl5_14
  <=> k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f2137,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))
    | ~ spl5_5 ),
    inference(superposition,[],[f65,f103])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f2121,plain,
    ( spl5_2
    | ~ spl5_36 ),
    inference(avatar_contradiction_clause,[],[f2120])).

fof(f2120,plain,
    ( $false
    | spl5_2
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f2119,f88])).

fof(f88,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2119,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f2111,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f2111,plain,
    ( sK2 = k5_xboole_0(sK1,sK1)
    | ~ spl5_36 ),
    inference(superposition,[],[f684,f2061])).

fof(f2061,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f2059])).

fof(f684,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f243,f128])).

fof(f128,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f64,f53])).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f243,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f57,f54])).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f2090,plain,
    ( ~ spl5_1
    | spl5_7
    | ~ spl5_38 ),
    inference(avatar_contradiction_clause,[],[f2089])).

fof(f2089,plain,
    ( $false
    | ~ spl5_1
    | spl5_7
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f2086,f149])).

fof(f149,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f2086,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_38 ),
    inference(resolution,[],[f2083,f1655])).

fof(f1655,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r1_tarski(sK1,X1) )
    | ~ spl5_1 ),
    inference(superposition,[],[f69,f83])).

fof(f83,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_1
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f2083,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f2081])).

fof(f2081,plain,
    ( spl5_38
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f2084,plain,
    ( spl5_38
    | ~ spl5_1
    | spl5_37 ),
    inference(avatar_split_clause,[],[f2077,f2073,f82,f2081])).

fof(f2073,plain,
    ( spl5_37
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f2077,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_1
    | spl5_37 ),
    inference(resolution,[],[f2075,f1656])).

fof(f1656,plain,
    ( ! [X2] :
        ( r1_xboole_0(sK1,X2)
        | r2_hidden(sK0,X2) )
    | ~ spl5_1 ),
    inference(superposition,[],[f70,f83])).

fof(f2075,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_37 ),
    inference(avatar_component_clause,[],[f2073])).

fof(f2076,plain,
    ( ~ spl5_37
    | spl5_35 ),
    inference(avatar_split_clause,[],[f2065,f2055,f2073])).

fof(f2065,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_35 ),
    inference(resolution,[],[f2057,f159])).

fof(f2057,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK1,sK2))
    | spl5_35 ),
    inference(avatar_component_clause,[],[f2055])).

fof(f1672,plain,
    ( spl5_32
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1651,f271,f82,f1669])).

fof(f1651,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f273,f83])).

fof(f273,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f271])).

fof(f1646,plain,
    ( ~ spl5_13
    | spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f787,f110,f82,f198])).

fof(f787,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ r2_hidden(sK0,sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f188,f112])).

fof(f188,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,k1_tarski(X9))
      | k1_tarski(X9) = X8
      | ~ r2_hidden(X9,X8) ) ),
    inference(resolution,[],[f60,f69])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f536,plain,
    ( spl5_3
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f535,f382,f91])).

fof(f91,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f535,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f532,f114])).

fof(f532,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl5_20 ),
    inference(resolution,[],[f384,f60])).

fof(f384,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f382])).

fof(f303,plain,
    ( ~ spl5_16
    | spl5_7 ),
    inference(avatar_split_clause,[],[f292,f147,f300])).

fof(f292,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_7 ),
    inference(resolution,[],[f115,f149])).

fof(f104,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f99,plain,
    ( ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f49,f95,f82])).

fof(f49,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f50,f95,f91])).

fof(f50,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f51,f86,f82])).

fof(f51,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (28456)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (28460)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (28459)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (28463)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (28476)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (28454)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (28472)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (28462)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (28471)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (28461)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (28468)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (28465)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (28478)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (28455)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (28469)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (28477)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (28453)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (28481)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (28457)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (28475)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (28464)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (28482)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (28470)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (28474)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (28466)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (28473)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (28467)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (28482)Refutation not found, incomplete strategy% (28482)------------------------------
% 0.21/0.56  % (28482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28482)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28482)Memory used [KB]: 1663
% 0.21/0.56  % (28482)Time elapsed: 0.114 s
% 0.21/0.56  % (28482)------------------------------
% 0.21/0.56  % (28482)------------------------------
% 0.21/0.56  % (28469)Refutation not found, incomplete strategy% (28469)------------------------------
% 0.21/0.56  % (28469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28469)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28469)Memory used [KB]: 10618
% 0.21/0.56  % (28469)Time elapsed: 0.139 s
% 0.21/0.56  % (28469)------------------------------
% 0.21/0.56  % (28469)------------------------------
% 0.21/0.57  % (28458)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (28480)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.58  % (28479)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.98/0.62  % (28456)Refutation not found, incomplete strategy% (28456)------------------------------
% 1.98/0.62  % (28456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.63  % (28456)Termination reason: Refutation not found, incomplete strategy
% 2.03/0.63  
% 2.03/0.63  % (28456)Memory used [KB]: 6140
% 2.03/0.63  % (28456)Time elapsed: 0.204 s
% 2.03/0.63  % (28456)------------------------------
% 2.03/0.63  % (28456)------------------------------
% 2.03/0.64  % (28465)Refutation not found, incomplete strategy% (28465)------------------------------
% 2.03/0.64  % (28465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.66  % (28465)Termination reason: Refutation not found, incomplete strategy
% 2.03/0.66  
% 2.03/0.66  % (28465)Memory used [KB]: 11641
% 2.03/0.66  % (28465)Time elapsed: 0.211 s
% 2.03/0.66  % (28465)------------------------------
% 2.03/0.66  % (28465)------------------------------
% 2.69/0.72  % (28484)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.69/0.74  % (28485)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.69/0.74  % (28486)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.69/0.75  % (28474)Refutation found. Thanks to Tanya!
% 2.69/0.75  % SZS status Theorem for theBenchmark
% 2.69/0.75  % SZS output start Proof for theBenchmark
% 2.69/0.75  fof(f2510,plain,(
% 2.69/0.75    $false),
% 2.69/0.75    inference(avatar_sat_refutation,[],[f89,f98,f99,f104,f303,f536,f1646,f1672,f2076,f2084,f2090,f2121,f2149,f2150,f2167,f2471,f2494,f2496,f2508])).
% 2.69/0.75  fof(f2508,plain,(
% 2.69/0.75    ~spl5_16 | spl5_20),
% 2.69/0.75    inference(avatar_split_clause,[],[f583,f382,f300])).
% 2.69/0.75  fof(f300,plain,(
% 2.69/0.75    spl5_16 <=> v1_xboole_0(sK1)),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.69/0.75  fof(f382,plain,(
% 2.69/0.75    spl5_20 <=> r1_tarski(sK1,k1_xboole_0)),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.69/0.75  fof(f583,plain,(
% 2.69/0.75    ~v1_xboole_0(sK1) | spl5_20),
% 2.69/0.75    inference(resolution,[],[f383,f115])).
% 2.69/0.75  fof(f115,plain,(
% 2.69/0.75    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 2.69/0.75    inference(superposition,[],[f114,f52])).
% 2.69/0.75  fof(f52,plain,(
% 2.69/0.75    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f33])).
% 2.69/0.75  fof(f33,plain,(
% 2.69/0.75    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.69/0.75    inference(ennf_transformation,[],[f4])).
% 2.69/0.75  fof(f4,axiom,(
% 2.69/0.75    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.69/0.75  fof(f114,plain,(
% 2.69/0.75    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.69/0.75    inference(superposition,[],[f76,f55])).
% 2.69/0.75  fof(f55,plain,(
% 2.69/0.75    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f13])).
% 2.69/0.75  fof(f13,axiom,(
% 2.69/0.75    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.69/0.75  fof(f76,plain,(
% 2.69/0.75    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f11])).
% 2.69/0.75  fof(f11,axiom,(
% 2.69/0.75    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.69/0.75  fof(f383,plain,(
% 2.69/0.75    ~r1_tarski(sK1,k1_xboole_0) | spl5_20),
% 2.69/0.75    inference(avatar_component_clause,[],[f382])).
% 2.69/0.75  fof(f2496,plain,(
% 2.69/0.75    spl5_16 | ~spl5_43 | ~spl5_6),
% 2.69/0.75    inference(avatar_split_clause,[],[f2457,f110,f2461,f300])).
% 2.69/0.75  fof(f2461,plain,(
% 2.69/0.75    spl5_43 <=> r1_xboole_0(k1_tarski(sK0),sK1)),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 2.69/0.75  fof(f110,plain,(
% 2.69/0.75    spl5_6 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.69/0.75  fof(f2457,plain,(
% 2.69/0.75    ~r1_xboole_0(k1_tarski(sK0),sK1) | v1_xboole_0(sK1) | ~spl5_6),
% 2.69/0.75    inference(resolution,[],[f458,f112])).
% 2.69/0.75  fof(f112,plain,(
% 2.69/0.75    r1_tarski(sK1,k1_tarski(sK0)) | ~spl5_6),
% 2.69/0.75    inference(avatar_component_clause,[],[f110])).
% 2.69/0.75  fof(f458,plain,(
% 2.69/0.75    ( ! [X26,X25] : (~r1_tarski(X26,X25) | ~r1_xboole_0(X25,X26) | v1_xboole_0(X26)) )),
% 2.69/0.75    inference(superposition,[],[f159,f136])).
% 2.69/0.75  fof(f136,plain,(
% 2.69/0.75    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = X3 | ~r1_tarski(X3,X4)) )),
% 2.69/0.75    inference(superposition,[],[f61,f63])).
% 2.69/0.75  fof(f63,plain,(
% 2.69/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f1])).
% 2.69/0.75  fof(f1,axiom,(
% 2.69/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.69/0.75  fof(f61,plain,(
% 2.69/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f34])).
% 2.69/0.75  fof(f34,plain,(
% 2.69/0.75    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.69/0.75    inference(ennf_transformation,[],[f12])).
% 2.69/0.75  fof(f12,axiom,(
% 2.69/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.69/0.75  fof(f159,plain,(
% 2.69/0.75    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.69/0.75    inference(resolution,[],[f75,f72])).
% 2.69/0.75  fof(f72,plain,(
% 2.69/0.75    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f45])).
% 2.69/0.75  fof(f45,plain,(
% 2.69/0.75    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0))),
% 2.69/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f44])).
% 2.69/0.75  fof(f44,plain,(
% 2.69/0.75    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.69/0.75    introduced(choice_axiom,[])).
% 2.69/0.75  fof(f37,plain,(
% 2.69/0.75    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 2.69/0.75    inference(ennf_transformation,[],[f31])).
% 2.69/0.75  fof(f31,plain,(
% 2.69/0.75    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 2.69/0.75    inference(unused_predicate_definition_removal,[],[f3])).
% 2.69/0.75  fof(f3,axiom,(
% 2.69/0.75    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.69/0.75  fof(f75,plain,(
% 2.69/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f47])).
% 2.69/0.75  fof(f47,plain,(
% 2.69/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.69/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f46])).
% 2.69/0.75  fof(f46,plain,(
% 2.69/0.75    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.69/0.75    introduced(choice_axiom,[])).
% 2.69/0.75  fof(f38,plain,(
% 2.69/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.69/0.75    inference(ennf_transformation,[],[f30])).
% 2.69/0.75  fof(f30,plain,(
% 2.69/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.69/0.75    inference(rectify,[],[f5])).
% 2.69/0.75  fof(f5,axiom,(
% 2.69/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.69/0.75  fof(f2494,plain,(
% 2.69/0.75    ~spl5_7 | spl5_4 | ~spl5_5),
% 2.69/0.75    inference(avatar_split_clause,[],[f390,f101,f95,f147])).
% 2.69/0.75  fof(f147,plain,(
% 2.69/0.75    spl5_7 <=> r1_tarski(sK1,sK2)),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.69/0.75  fof(f95,plain,(
% 2.69/0.75    spl5_4 <=> sK2 = k1_tarski(sK0)),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.69/0.75  fof(f101,plain,(
% 2.69/0.75    spl5_5 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.69/0.75  fof(f390,plain,(
% 2.69/0.75    sK2 = k1_tarski(sK0) | ~r1_tarski(sK1,sK2) | ~spl5_5),
% 2.69/0.75    inference(superposition,[],[f103,f62])).
% 2.69/0.75  fof(f62,plain,(
% 2.69/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f35])).
% 2.69/0.75  fof(f35,plain,(
% 2.69/0.75    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.69/0.75    inference(ennf_transformation,[],[f9])).
% 2.69/0.75  fof(f9,axiom,(
% 2.69/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.69/0.75  fof(f103,plain,(
% 2.69/0.75    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl5_5),
% 2.69/0.75    inference(avatar_component_clause,[],[f101])).
% 2.69/0.75  fof(f2471,plain,(
% 2.69/0.75    spl5_13 | spl5_43),
% 2.69/0.75    inference(avatar_contradiction_clause,[],[f2470])).
% 2.69/0.75  fof(f2470,plain,(
% 2.69/0.75    $false | (spl5_13 | spl5_43)),
% 2.69/0.75    inference(subsumption_resolution,[],[f2466,f200])).
% 2.69/0.75  fof(f200,plain,(
% 2.69/0.75    ~r2_hidden(sK0,sK1) | spl5_13),
% 2.69/0.75    inference(avatar_component_clause,[],[f198])).
% 2.69/0.75  fof(f198,plain,(
% 2.69/0.75    spl5_13 <=> r2_hidden(sK0,sK1)),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.69/0.75  fof(f2466,plain,(
% 2.69/0.75    r2_hidden(sK0,sK1) | spl5_43),
% 2.69/0.75    inference(resolution,[],[f2463,f70])).
% 2.69/0.75  fof(f70,plain,(
% 2.69/0.75    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f36])).
% 2.69/0.75  fof(f36,plain,(
% 2.69/0.75    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.69/0.75    inference(ennf_transformation,[],[f26])).
% 2.69/0.75  fof(f26,axiom,(
% 2.69/0.75    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.69/0.75  fof(f2463,plain,(
% 2.69/0.75    ~r1_xboole_0(k1_tarski(sK0),sK1) | spl5_43),
% 2.69/0.75    inference(avatar_component_clause,[],[f2461])).
% 2.69/0.75  fof(f2167,plain,(
% 2.69/0.75    ~spl5_35 | spl5_36 | ~spl5_32),
% 2.69/0.75    inference(avatar_split_clause,[],[f2164,f1669,f2059,f2055])).
% 2.69/0.75  fof(f2055,plain,(
% 2.69/0.75    spl5_35 <=> v1_xboole_0(k3_xboole_0(sK1,sK2))),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 2.69/0.75  fof(f2059,plain,(
% 2.69/0.75    spl5_36 <=> sK1 = k5_xboole_0(sK1,sK2)),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 2.69/0.75  fof(f1669,plain,(
% 2.69/0.75    spl5_32 <=> k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.69/0.75  fof(f2164,plain,(
% 2.69/0.75    sK1 = k5_xboole_0(sK1,sK2) | ~v1_xboole_0(k3_xboole_0(sK1,sK2)) | ~spl5_32),
% 2.69/0.75    inference(superposition,[],[f288,f1671])).
% 2.69/0.75  fof(f1671,plain,(
% 2.69/0.75    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | ~spl5_32),
% 2.69/0.75    inference(avatar_component_clause,[],[f1669])).
% 2.69/0.75  fof(f288,plain,(
% 2.69/0.75    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = X1 | ~v1_xboole_0(X0)) )),
% 2.69/0.75    inference(superposition,[],[f207,f52])).
% 2.69/0.75  fof(f207,plain,(
% 2.69/0.75    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.69/0.75    inference(forward_demodulation,[],[f202,f53])).
% 2.69/0.75  fof(f53,plain,(
% 2.69/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.69/0.75    inference(cnf_transformation,[],[f14])).
% 2.69/0.75  fof(f14,axiom,(
% 2.69/0.75    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.69/0.75  fof(f202,plain,(
% 2.69/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 2.69/0.75    inference(superposition,[],[f73,f55])).
% 2.69/0.75  fof(f73,plain,(
% 2.69/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.69/0.75    inference(cnf_transformation,[],[f8])).
% 2.69/0.75  fof(f8,axiom,(
% 2.69/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.69/0.75  fof(f2150,plain,(
% 2.69/0.75    spl5_6 | ~spl5_5),
% 2.69/0.75    inference(avatar_split_clause,[],[f2139,f101,f110])).
% 2.69/0.75  fof(f2139,plain,(
% 2.69/0.75    r1_tarski(sK1,k1_tarski(sK0)) | ~spl5_5),
% 2.69/0.75    inference(superposition,[],[f67,f103])).
% 2.69/0.75  fof(f67,plain,(
% 2.69/0.75    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.69/0.75    inference(cnf_transformation,[],[f15])).
% 2.69/0.75  fof(f15,axiom,(
% 2.69/0.75    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.69/0.75  fof(f2149,plain,(
% 2.69/0.75    spl5_14 | ~spl5_5),
% 2.69/0.75    inference(avatar_split_clause,[],[f2137,f101,f271])).
% 2.69/0.75  fof(f271,plain,(
% 2.69/0.75    spl5_14 <=> k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.69/0.75  fof(f2137,plain,(
% 2.69/0.75    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) | ~spl5_5),
% 2.69/0.75    inference(superposition,[],[f65,f103])).
% 2.69/0.75  fof(f65,plain,(
% 2.69/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.69/0.75    inference(cnf_transformation,[],[f7])).
% 2.69/0.75  fof(f7,axiom,(
% 2.69/0.75    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.69/0.75  fof(f2121,plain,(
% 2.69/0.75    spl5_2 | ~spl5_36),
% 2.69/0.75    inference(avatar_contradiction_clause,[],[f2120])).
% 2.69/0.75  fof(f2120,plain,(
% 2.69/0.75    $false | (spl5_2 | ~spl5_36)),
% 2.69/0.75    inference(subsumption_resolution,[],[f2119,f88])).
% 2.69/0.75  fof(f88,plain,(
% 2.69/0.75    k1_xboole_0 != sK2 | spl5_2),
% 2.69/0.75    inference(avatar_component_clause,[],[f86])).
% 2.69/0.75  fof(f86,plain,(
% 2.69/0.75    spl5_2 <=> k1_xboole_0 = sK2),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.69/0.75  fof(f2119,plain,(
% 2.69/0.75    k1_xboole_0 = sK2 | ~spl5_36),
% 2.69/0.75    inference(forward_demodulation,[],[f2111,f54])).
% 2.69/0.75  fof(f54,plain,(
% 2.69/0.75    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f17])).
% 2.69/0.75  fof(f17,axiom,(
% 2.69/0.75    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.69/0.75  fof(f2111,plain,(
% 2.69/0.75    sK2 = k5_xboole_0(sK1,sK1) | ~spl5_36),
% 2.69/0.75    inference(superposition,[],[f684,f2061])).
% 2.69/0.75  fof(f2061,plain,(
% 2.69/0.75    sK1 = k5_xboole_0(sK1,sK2) | ~spl5_36),
% 2.69/0.75    inference(avatar_component_clause,[],[f2059])).
% 2.69/0.75  fof(f684,plain,(
% 2.69/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.69/0.75    inference(forward_demodulation,[],[f243,f128])).
% 2.69/0.75  fof(f128,plain,(
% 2.69/0.75    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.69/0.75    inference(superposition,[],[f64,f53])).
% 2.69/0.75  fof(f64,plain,(
% 2.69/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f2])).
% 2.69/0.75  fof(f2,axiom,(
% 2.69/0.75    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.69/0.75  fof(f243,plain,(
% 2.69/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.69/0.75    inference(superposition,[],[f57,f54])).
% 2.69/0.75  fof(f57,plain,(
% 2.69/0.75    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.69/0.75    inference(cnf_transformation,[],[f16])).
% 2.69/0.75  fof(f16,axiom,(
% 2.69/0.75    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.69/0.75  fof(f2090,plain,(
% 2.69/0.75    ~spl5_1 | spl5_7 | ~spl5_38),
% 2.69/0.75    inference(avatar_contradiction_clause,[],[f2089])).
% 2.69/0.75  fof(f2089,plain,(
% 2.69/0.75    $false | (~spl5_1 | spl5_7 | ~spl5_38)),
% 2.69/0.75    inference(subsumption_resolution,[],[f2086,f149])).
% 2.69/0.75  fof(f149,plain,(
% 2.69/0.75    ~r1_tarski(sK1,sK2) | spl5_7),
% 2.69/0.75    inference(avatar_component_clause,[],[f147])).
% 2.69/0.75  fof(f2086,plain,(
% 2.69/0.75    r1_tarski(sK1,sK2) | (~spl5_1 | ~spl5_38)),
% 2.69/0.75    inference(resolution,[],[f2083,f1655])).
% 2.69/0.75  fof(f1655,plain,(
% 2.69/0.75    ( ! [X1] : (~r2_hidden(sK0,X1) | r1_tarski(sK1,X1)) ) | ~spl5_1),
% 2.69/0.75    inference(superposition,[],[f69,f83])).
% 2.69/0.75  fof(f83,plain,(
% 2.69/0.75    sK1 = k1_tarski(sK0) | ~spl5_1),
% 2.69/0.75    inference(avatar_component_clause,[],[f82])).
% 2.69/0.75  fof(f82,plain,(
% 2.69/0.75    spl5_1 <=> sK1 = k1_tarski(sK0)),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.69/0.75  fof(f69,plain,(
% 2.69/0.75    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f43])).
% 2.69/0.75  fof(f43,plain,(
% 2.69/0.75    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.69/0.75    inference(nnf_transformation,[],[f25])).
% 2.69/0.75  fof(f25,axiom,(
% 2.69/0.75    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.69/0.75  fof(f2083,plain,(
% 2.69/0.75    r2_hidden(sK0,sK2) | ~spl5_38),
% 2.69/0.75    inference(avatar_component_clause,[],[f2081])).
% 2.69/0.75  fof(f2081,plain,(
% 2.69/0.75    spl5_38 <=> r2_hidden(sK0,sK2)),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 2.69/0.75  fof(f2084,plain,(
% 2.69/0.75    spl5_38 | ~spl5_1 | spl5_37),
% 2.69/0.75    inference(avatar_split_clause,[],[f2077,f2073,f82,f2081])).
% 2.69/0.75  fof(f2073,plain,(
% 2.69/0.75    spl5_37 <=> r1_xboole_0(sK1,sK2)),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 2.69/0.75  fof(f2077,plain,(
% 2.69/0.75    r2_hidden(sK0,sK2) | (~spl5_1 | spl5_37)),
% 2.69/0.75    inference(resolution,[],[f2075,f1656])).
% 2.69/0.75  fof(f1656,plain,(
% 2.69/0.75    ( ! [X2] : (r1_xboole_0(sK1,X2) | r2_hidden(sK0,X2)) ) | ~spl5_1),
% 2.69/0.75    inference(superposition,[],[f70,f83])).
% 2.69/0.75  fof(f2075,plain,(
% 2.69/0.75    ~r1_xboole_0(sK1,sK2) | spl5_37),
% 2.69/0.75    inference(avatar_component_clause,[],[f2073])).
% 2.69/0.75  fof(f2076,plain,(
% 2.69/0.75    ~spl5_37 | spl5_35),
% 2.69/0.75    inference(avatar_split_clause,[],[f2065,f2055,f2073])).
% 2.69/0.75  fof(f2065,plain,(
% 2.69/0.75    ~r1_xboole_0(sK1,sK2) | spl5_35),
% 2.69/0.75    inference(resolution,[],[f2057,f159])).
% 2.69/0.75  fof(f2057,plain,(
% 2.69/0.75    ~v1_xboole_0(k3_xboole_0(sK1,sK2)) | spl5_35),
% 2.69/0.75    inference(avatar_component_clause,[],[f2055])).
% 2.69/0.75  fof(f1672,plain,(
% 2.69/0.75    spl5_32 | ~spl5_1 | ~spl5_14),
% 2.69/0.75    inference(avatar_split_clause,[],[f1651,f271,f82,f1669])).
% 2.69/0.75  fof(f1651,plain,(
% 2.69/0.75    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | (~spl5_1 | ~spl5_14)),
% 2.69/0.75    inference(backward_demodulation,[],[f273,f83])).
% 2.69/0.75  fof(f273,plain,(
% 2.69/0.75    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) | ~spl5_14),
% 2.69/0.75    inference(avatar_component_clause,[],[f271])).
% 2.69/0.75  fof(f1646,plain,(
% 2.69/0.75    ~spl5_13 | spl5_1 | ~spl5_6),
% 2.69/0.75    inference(avatar_split_clause,[],[f787,f110,f82,f198])).
% 2.69/0.75  fof(f787,plain,(
% 2.69/0.75    sK1 = k1_tarski(sK0) | ~r2_hidden(sK0,sK1) | ~spl5_6),
% 2.69/0.75    inference(resolution,[],[f188,f112])).
% 2.69/0.75  fof(f188,plain,(
% 2.69/0.75    ( ! [X8,X9] : (~r1_tarski(X8,k1_tarski(X9)) | k1_tarski(X9) = X8 | ~r2_hidden(X9,X8)) )),
% 2.69/0.75    inference(resolution,[],[f60,f69])).
% 2.69/0.75  fof(f60,plain,(
% 2.69/0.75    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.69/0.75    inference(cnf_transformation,[],[f42])).
% 2.69/0.75  fof(f42,plain,(
% 2.69/0.75    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.69/0.75    inference(flattening,[],[f41])).
% 2.69/0.75  fof(f41,plain,(
% 2.69/0.75    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.69/0.75    inference(nnf_transformation,[],[f6])).
% 2.69/0.75  fof(f6,axiom,(
% 2.69/0.75    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.69/0.75  fof(f536,plain,(
% 2.69/0.75    spl5_3 | ~spl5_20),
% 2.69/0.75    inference(avatar_split_clause,[],[f535,f382,f91])).
% 2.69/0.75  fof(f91,plain,(
% 2.69/0.75    spl5_3 <=> k1_xboole_0 = sK1),
% 2.69/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.69/0.75  fof(f535,plain,(
% 2.69/0.75    k1_xboole_0 = sK1 | ~spl5_20),
% 2.69/0.75    inference(subsumption_resolution,[],[f532,f114])).
% 2.69/0.75  fof(f532,plain,(
% 2.69/0.75    k1_xboole_0 = sK1 | ~r1_tarski(k1_xboole_0,sK1) | ~spl5_20),
% 2.69/0.75    inference(resolution,[],[f384,f60])).
% 2.69/0.75  fof(f384,plain,(
% 2.69/0.75    r1_tarski(sK1,k1_xboole_0) | ~spl5_20),
% 2.69/0.75    inference(avatar_component_clause,[],[f382])).
% 2.69/0.75  fof(f303,plain,(
% 2.69/0.75    ~spl5_16 | spl5_7),
% 2.69/0.75    inference(avatar_split_clause,[],[f292,f147,f300])).
% 2.69/0.75  fof(f292,plain,(
% 2.69/0.75    ~v1_xboole_0(sK1) | spl5_7),
% 2.69/0.75    inference(resolution,[],[f115,f149])).
% 2.69/0.75  fof(f104,plain,(
% 2.69/0.75    spl5_5),
% 2.69/0.75    inference(avatar_split_clause,[],[f48,f101])).
% 2.69/0.75  fof(f48,plain,(
% 2.69/0.75    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.69/0.75    inference(cnf_transformation,[],[f40])).
% 2.69/0.75  fof(f40,plain,(
% 2.69/0.75    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.69/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f39])).
% 2.69/0.75  fof(f39,plain,(
% 2.69/0.75    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.69/0.75    introduced(choice_axiom,[])).
% 2.69/0.75  fof(f32,plain,(
% 2.69/0.75    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.69/0.75    inference(ennf_transformation,[],[f29])).
% 2.69/0.75  fof(f29,negated_conjecture,(
% 2.69/0.75    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.69/0.75    inference(negated_conjecture,[],[f28])).
% 2.69/0.75  fof(f28,conjecture,(
% 2.69/0.75    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.69/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.69/0.75  fof(f99,plain,(
% 2.69/0.75    ~spl5_1 | ~spl5_4),
% 2.69/0.75    inference(avatar_split_clause,[],[f49,f95,f82])).
% 2.69/0.75  fof(f49,plain,(
% 2.69/0.75    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.69/0.75    inference(cnf_transformation,[],[f40])).
% 2.69/0.75  fof(f98,plain,(
% 2.69/0.75    ~spl5_3 | ~spl5_4),
% 2.69/0.75    inference(avatar_split_clause,[],[f50,f95,f91])).
% 2.69/0.75  fof(f50,plain,(
% 2.69/0.75    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.69/0.75    inference(cnf_transformation,[],[f40])).
% 2.69/0.75  fof(f89,plain,(
% 2.69/0.75    ~spl5_1 | ~spl5_2),
% 2.69/0.75    inference(avatar_split_clause,[],[f51,f86,f82])).
% 2.69/0.75  fof(f51,plain,(
% 2.69/0.75    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 2.69/0.75    inference(cnf_transformation,[],[f40])).
% 2.69/0.75  % SZS output end Proof for theBenchmark
% 2.69/0.75  % (28474)------------------------------
% 2.69/0.75  % (28474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.69/0.75  % (28474)Termination reason: Refutation
% 2.69/0.75  
% 2.69/0.75  % (28474)Memory used [KB]: 7675
% 2.69/0.75  % (28474)Time elapsed: 0.295 s
% 2.69/0.75  % (28474)------------------------------
% 2.69/0.75  % (28474)------------------------------
% 2.69/0.75  % (28452)Success in time 0.391 s
%------------------------------------------------------------------------------
