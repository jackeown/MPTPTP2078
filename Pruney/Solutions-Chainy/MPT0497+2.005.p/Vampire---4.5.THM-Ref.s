%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 199 expanded)
%              Number of leaves         :   23 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  240 ( 478 expanded)
%              Number of equality atoms :   81 ( 165 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f691,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f56,f61,f152,f171,f213,f645,f647,f649,f653,f672,f688])).

fof(f688,plain,
    ( spl2_4
    | ~ spl2_22
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f687,f669,f211,f66])).

fof(f66,plain,
    ( spl2_4
  <=> k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f211,plain,
    ( spl2_22
  <=> ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f669,plain,
    ( spl2_53
  <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f687,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_22
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f681,f413])).

fof(f413,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_22 ),
    inference(resolution,[],[f412,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f412,plain,
    ( ! [X1] : r1_xboole_0(X1,k1_xboole_0)
    | ~ spl2_22 ),
    inference(resolution,[],[f408,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f408,plain,
    ( ! [X1] : r1_xboole_0(k1_xboole_0,X1)
    | ~ spl2_22 ),
    inference(superposition,[],[f35,f214])).

fof(f214,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_relat_1(sK1),X0),X0)
    | ~ spl2_22 ),
    inference(resolution,[],[f212,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f212,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f211])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f681,plain,
    ( k4_xboole_0(k1_relat_1(sK1),sK0) = k4_xboole_0(k1_relat_1(sK1),k1_xboole_0)
    | ~ spl2_53 ),
    inference(superposition,[],[f38,f671])).

fof(f671,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f669])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f672,plain,
    ( spl2_53
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f667,f58,f48,f669])).

fof(f48,plain,
    ( spl2_1
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f58,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f667,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f664,f31])).

fof(f31,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f664,plain,
    ( k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(superposition,[],[f62,f49])).

fof(f49,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f62,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_3 ),
    inference(resolution,[],[f60,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f60,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f653,plain,
    ( spl2_46
    | ~ spl2_15
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f494,f211,f168,f473])).

fof(f473,plain,
    ( spl2_46
  <=> k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f168,plain,
    ( spl2_15
  <=> k3_xboole_0(sK0,k1_relat_1(sK1)) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f494,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_15
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f170,f455])).

fof(f455,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f427,f436])).

fof(f436,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl2_22 ),
    inference(superposition,[],[f415,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f415,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)
    | ~ spl2_22 ),
    inference(superposition,[],[f411,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f411,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_22 ),
    inference(resolution,[],[f408,f43])).

fof(f427,plain,
    ( ! [X2] : k3_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,X2)
    | ~ spl2_22 ),
    inference(superposition,[],[f37,f413])).

fof(f170,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK1)) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f168])).

fof(f649,plain,
    ( spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f165,f66,f52])).

fof(f52,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f165,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_4 ),
    inference(superposition,[],[f44,f68])).

fof(f68,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f647,plain,
    ( ~ spl2_3
    | spl2_52 ),
    inference(avatar_split_clause,[],[f646,f642,f58])).

fof(f642,plain,
    ( spl2_52
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f646,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_52 ),
    inference(resolution,[],[f644,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f644,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_52 ),
    inference(avatar_component_clause,[],[f642])).

fof(f645,plain,
    ( ~ spl2_52
    | spl2_1
    | ~ spl2_3
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f637,f473,f58,f48,f642])).

fof(f637,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_3
    | ~ spl2_46 ),
    inference(trivial_inequality_removal,[],[f636])).

fof(f636,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_3
    | ~ spl2_46 ),
    inference(superposition,[],[f558,f475])).

fof(f475,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f473])).

fof(f558,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(X0,k1_relat_1(sK1))
        | k1_xboole_0 = k7_relat_1(sK1,X0)
        | ~ v1_relat_1(k7_relat_1(sK1,X0)) )
    | ~ spl2_3 ),
    inference(superposition,[],[f209,f36])).

fof(f209,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),X1)
        | k1_xboole_0 = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(k7_relat_1(sK1,X1)) )
    | ~ spl2_3 ),
    inference(superposition,[],[f33,f62])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f213,plain,
    ( ~ spl2_3
    | spl2_22
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f208,f58,f211,f58])).

fof(f208,plain,
    ( ! [X0] :
        ( r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_3 ),
    inference(superposition,[],[f40,f62])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f171,plain,
    ( spl2_15
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f166,f66,f168])).

fof(f166,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK1)) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f164,f36])).

fof(f164,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK0) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl2_4 ),
    inference(superposition,[],[f37,f68])).

fof(f152,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f150,f52,f66])).

fof(f150,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f61,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f24,plain,
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

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f56,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f29,f52,f48])).

fof(f29,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f30,f52,f48])).

fof(f30,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:21:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (25232)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.46  % (25229)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (25230)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (25231)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (25235)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (25241)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (25228)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (25239)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (25233)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (25240)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (25237)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (25238)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (25237)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (25227)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (25234)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f691,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f55,f56,f61,f152,f171,f213,f645,f647,f649,f653,f672,f688])).
% 0.22/0.50  fof(f688,plain,(
% 0.22/0.50    spl2_4 | ~spl2_22 | ~spl2_53),
% 0.22/0.50    inference(avatar_split_clause,[],[f687,f669,f211,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl2_4 <=> k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    spl2_22 <=> ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.50  fof(f669,plain,(
% 0.22/0.50    spl2_53 <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.22/0.50  fof(f687,plain,(
% 0.22/0.50    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_22 | ~spl2_53)),
% 0.22/0.50    inference(forward_demodulation,[],[f681,f413])).
% 0.22/0.50  fof(f413,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_22),
% 0.22/0.50    inference(resolution,[],[f412,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.50  fof(f412,plain,(
% 0.22/0.50    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) ) | ~spl2_22),
% 0.22/0.50    inference(resolution,[],[f408,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.50  fof(f408,plain,(
% 0.22/0.50    ( ! [X1] : (r1_xboole_0(k1_xboole_0,X1)) ) | ~spl2_22),
% 0.22/0.50    inference(superposition,[],[f35,f214])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_relat_1(sK1),X0),X0)) ) | ~spl2_22),
% 0.22/0.50    inference(resolution,[],[f212,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.50    inference(nnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)) ) | ~spl2_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f211])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.50  fof(f681,plain,(
% 0.22/0.50    k4_xboole_0(k1_relat_1(sK1),sK0) = k4_xboole_0(k1_relat_1(sK1),k1_xboole_0) | ~spl2_53),
% 0.22/0.50    inference(superposition,[],[f38,f671])).
% 0.22/0.50  fof(f671,plain,(
% 0.22/0.50    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_53),
% 0.22/0.50    inference(avatar_component_clause,[],[f669])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.50  fof(f672,plain,(
% 0.22/0.50    spl2_53 | ~spl2_1 | ~spl2_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f667,f58,f48,f669])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    spl2_1 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl2_3 <=> v1_relat_1(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.50  fof(f667,plain,(
% 0.22/0.50    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_1 | ~spl2_3)),
% 0.22/0.50    inference(forward_demodulation,[],[f664,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.50  fof(f664,plain,(
% 0.22/0.50    k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_1 | ~spl2_3)),
% 0.22/0.50    inference(superposition,[],[f62,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f48])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl2_3),
% 0.22/0.50    inference(resolution,[],[f60,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    v1_relat_1(sK1) | ~spl2_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f58])).
% 0.22/0.50  fof(f653,plain,(
% 0.22/0.50    spl2_46 | ~spl2_15 | ~spl2_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f494,f211,f168,f473])).
% 0.22/0.50  fof(f473,plain,(
% 0.22/0.50    spl2_46 <=> k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    spl2_15 <=> k3_xboole_0(sK0,k1_relat_1(sK1)) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.50  fof(f494,plain,(
% 0.22/0.50    k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1)) | (~spl2_15 | ~spl2_22)),
% 0.22/0.50    inference(forward_demodulation,[],[f170,f455])).
% 0.22/0.50  fof(f455,plain,(
% 0.22/0.50    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | ~spl2_22),
% 0.22/0.50    inference(forward_demodulation,[],[f427,f436])).
% 0.22/0.50  fof(f436,plain,(
% 0.22/0.50    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | ~spl2_22),
% 0.22/0.50    inference(superposition,[],[f415,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.50  fof(f415,plain,(
% 0.22/0.50    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) ) | ~spl2_22),
% 0.22/0.50    inference(superposition,[],[f411,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.50  fof(f411,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl2_22),
% 0.22/0.50    inference(resolution,[],[f408,f43])).
% 0.22/0.50  fof(f427,plain,(
% 0.22/0.50    ( ! [X2] : (k3_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,X2)) ) | ~spl2_22),
% 0.22/0.50    inference(superposition,[],[f37,f413])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    k3_xboole_0(sK0,k1_relat_1(sK1)) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) | ~spl2_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f168])).
% 0.22/0.50  fof(f649,plain,(
% 0.22/0.50    spl2_2 | ~spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f165,f66,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    spl2_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_4),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    k1_relat_1(sK1) != k1_relat_1(sK1) | r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_4),
% 0.22/0.50    inference(superposition,[],[f44,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f647,plain,(
% 0.22/0.50    ~spl2_3 | spl2_52),
% 0.22/0.50    inference(avatar_split_clause,[],[f646,f642,f58])).
% 0.22/0.50  fof(f642,plain,(
% 0.22/0.50    spl2_52 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 0.22/0.50  fof(f646,plain,(
% 0.22/0.50    ~v1_relat_1(sK1) | spl2_52),
% 0.22/0.50    inference(resolution,[],[f644,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.50  fof(f644,plain,(
% 0.22/0.50    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_52),
% 0.22/0.50    inference(avatar_component_clause,[],[f642])).
% 0.22/0.50  fof(f645,plain,(
% 0.22/0.50    ~spl2_52 | spl2_1 | ~spl2_3 | ~spl2_46),
% 0.22/0.50    inference(avatar_split_clause,[],[f637,f473,f58,f48,f642])).
% 0.22/0.50  fof(f637,plain,(
% 0.22/0.50    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_3 | ~spl2_46)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f636])).
% 0.22/0.50  fof(f636,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_3 | ~spl2_46)),
% 0.22/0.50    inference(superposition,[],[f558,f475])).
% 0.22/0.50  fof(f475,plain,(
% 0.22/0.50    k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1)) | ~spl2_46),
% 0.22/0.50    inference(avatar_component_clause,[],[f473])).
% 0.22/0.50  fof(f558,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(X0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,X0) | ~v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_3),
% 0.22/0.50    inference(superposition,[],[f209,f36])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ( ! [X1] : (k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),X1) | k1_xboole_0 = k7_relat_1(sK1,X1) | ~v1_relat_1(k7_relat_1(sK1,X1))) ) | ~spl2_3),
% 0.22/0.50    inference(superposition,[],[f33,f62])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    ~spl2_3 | spl2_22 | ~spl2_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f208,f58,f211,f58])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0) | ~v1_relat_1(sK1)) ) | ~spl2_3),
% 0.22/0.50    inference(superposition,[],[f40,f62])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    spl2_15 | ~spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f166,f66,f168])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    k3_xboole_0(sK0,k1_relat_1(sK1)) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) | ~spl2_4),
% 0.22/0.50    inference(forward_demodulation,[],[f164,f36])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    k3_xboole_0(k1_relat_1(sK1),sK0) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) | ~spl2_4),
% 0.22/0.50    inference(superposition,[],[f37,f68])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    spl2_4 | ~spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f150,f52,f66])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_2),
% 0.22/0.50    inference(resolution,[],[f53,f43])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f52])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl2_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f58])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    v1_relat_1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.50    inference(negated_conjecture,[],[f13])).
% 0.22/0.50  fof(f13,conjecture,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl2_1 | spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f52,f48])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ~spl2_1 | ~spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f52,f48])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (25237)------------------------------
% 0.22/0.50  % (25237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25237)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (25237)Memory used [KB]: 11001
% 0.22/0.50  % (25237)Time elapsed: 0.072 s
% 0.22/0.50  % (25237)------------------------------
% 0.22/0.50  % (25237)------------------------------
% 0.22/0.50  % (25222)Success in time 0.141 s
%------------------------------------------------------------------------------
