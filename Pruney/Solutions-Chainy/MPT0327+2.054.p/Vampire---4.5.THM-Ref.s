%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:56 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 159 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  212 ( 313 expanded)
%              Number of equality atoms :   79 ( 126 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (18786)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f761,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f276,f285,f357,f659,f743,f760])).

fof(f760,plain,
    ( ~ spl2_15
    | spl2_31 ),
    inference(avatar_contradiction_clause,[],[f759])).

fof(f759,plain,
    ( $false
    | ~ spl2_15
    | spl2_31 ),
    inference(subsumption_resolution,[],[f757,f336])).

fof(f336,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl2_15
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f757,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl2_31 ),
    inference(trivial_inequality_removal,[],[f756])).

fof(f756,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl2_31 ),
    inference(superposition,[],[f742,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f742,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | spl2_31 ),
    inference(avatar_component_clause,[],[f740])).

fof(f740,plain,
    ( spl2_31
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f743,plain,
    ( ~ spl2_31
    | ~ spl2_15
    | spl2_24 ),
    inference(avatar_split_clause,[],[f738,f656,f335,f740])).

fof(f656,plain,
    ( spl2_24
  <=> sK1 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f738,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_15
    | spl2_24 ),
    inference(subsumption_resolution,[],[f737,f336])).

fof(f737,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl2_24 ),
    inference(superposition,[],[f658,f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f51,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f658,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0))
    | spl2_24 ),
    inference(avatar_component_clause,[],[f656])).

fof(f659,plain,
    ( ~ spl2_24
    | spl2_11
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f654,f335,f273,f656])).

fof(f273,plain,
    ( spl2_11
  <=> sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f654,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0))
    | spl2_11
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f625,f336])).

fof(f625,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0))
    | ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl2_11 ),
    inference(superposition,[],[f275,f603])).

fof(f603,plain,(
    ! [X2,X3] :
      ( k5_xboole_0(X2,X3) = k4_xboole_0(X3,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(backward_demodulation,[],[f157,f595])).

fof(f595,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f588,f181])).

fof(f181,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f180,f53])).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f180,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f179,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f179,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f51,f155])).

fof(f155,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f149,f53])).

fof(f149,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f49,f146])).

fof(f146,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f83,f58])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f83,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f47,f53])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f588,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f457,f49])).

fof(f457,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f456,f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f456,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f447,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f447,plain,(
    ! [X0] :
      ( k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f170,f210])).

fof(f210,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(subsumption_resolution,[],[f195,f68])).

fof(f195,plain,(
    ! [X1] :
      ( k1_xboole_0 = k5_xboole_0(X1,X1)
      | ~ r1_tarski(X1,X1) ) ),
    inference(superposition,[],[f162,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f162,plain,(
    ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2) ),
    inference(superposition,[],[f48,f50])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f157,plain,(
    ! [X2,X3] :
      ( k5_xboole_0(X2,X3) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X2))
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f48,f55])).

fof(f275,plain,
    ( sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f273])).

fof(f357,plain,
    ( ~ spl2_2
    | spl2_15 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | ~ spl2_2
    | spl2_15 ),
    inference(subsumption_resolution,[],[f354,f78])).

fof(f78,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f354,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_15 ),
    inference(resolution,[],[f337,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f337,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl2_15 ),
    inference(avatar_component_clause,[],[f335])).

fof(f285,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl2_10 ),
    inference(subsumption_resolution,[],[f280,f67])).

fof(f67,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f280,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl2_10 ),
    inference(resolution,[],[f271,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f271,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl2_10
  <=> r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f276,plain,
    ( ~ spl2_10
    | ~ spl2_11
    | spl2_1 ),
    inference(avatar_split_clause,[],[f261,f71,f273,f269])).

fof(f71,plain,
    ( spl2_1
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f261,plain,
    ( sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl2_1 ),
    inference(superposition,[],[f73,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f49,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f73,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f79,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f74,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.53  % (18787)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (18768)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (18779)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (18787)Refutation not found, incomplete strategy% (18787)------------------------------
% 0.21/0.53  % (18787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (18763)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.29/0.54  % (18760)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.29/0.54  % (18787)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (18787)Memory used [KB]: 1663
% 1.29/0.54  % (18787)Time elapsed: 0.119 s
% 1.29/0.54  % (18787)------------------------------
% 1.29/0.54  % (18787)------------------------------
% 1.29/0.54  % (18761)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.29/0.54  % (18758)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.29/0.54  % (18771)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.29/0.54  % (18768)Refutation not found, incomplete strategy% (18768)------------------------------
% 1.29/0.54  % (18768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (18768)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (18768)Memory used [KB]: 10746
% 1.29/0.54  % (18768)Time elapsed: 0.129 s
% 1.29/0.54  % (18768)------------------------------
% 1.29/0.54  % (18768)------------------------------
% 1.29/0.54  % (18762)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.29/0.55  % (18772)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.29/0.55  % (18759)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.29/0.55  % (18785)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.29/0.55  % (18785)Refutation not found, incomplete strategy% (18785)------------------------------
% 1.29/0.55  % (18785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (18785)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (18785)Memory used [KB]: 6140
% 1.29/0.55  % (18785)Time elapsed: 0.148 s
% 1.29/0.55  % (18785)------------------------------
% 1.29/0.55  % (18785)------------------------------
% 1.29/0.55  % (18783)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.29/0.55  % (18765)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.29/0.55  % (18766)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.29/0.55  % (18778)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.29/0.55  % (18777)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.29/0.55  % (18773)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.54/0.56  % (18781)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.54/0.56  % (18779)Refutation found. Thanks to Tanya!
% 1.54/0.56  % SZS status Theorem for theBenchmark
% 1.54/0.56  % (18775)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.54/0.56  % (18780)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.54/0.56  % SZS output start Proof for theBenchmark
% 1.54/0.56  % (18786)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.54/0.56  fof(f761,plain,(
% 1.54/0.56    $false),
% 1.54/0.56    inference(avatar_sat_refutation,[],[f74,f79,f276,f285,f357,f659,f743,f760])).
% 1.54/0.56  fof(f760,plain,(
% 1.54/0.56    ~spl2_15 | spl2_31),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f759])).
% 1.54/0.56  fof(f759,plain,(
% 1.54/0.56    $false | (~spl2_15 | spl2_31)),
% 1.54/0.56    inference(subsumption_resolution,[],[f757,f336])).
% 1.54/0.56  fof(f336,plain,(
% 1.54/0.56    r1_tarski(k1_tarski(sK0),sK1) | ~spl2_15),
% 1.54/0.56    inference(avatar_component_clause,[],[f335])).
% 1.54/0.56  fof(f335,plain,(
% 1.54/0.56    spl2_15 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.54/0.56  fof(f757,plain,(
% 1.54/0.56    ~r1_tarski(k1_tarski(sK0),sK1) | spl2_31),
% 1.54/0.56    inference(trivial_inequality_removal,[],[f756])).
% 1.54/0.56  fof(f756,plain,(
% 1.54/0.56    sK1 != sK1 | ~r1_tarski(k1_tarski(sK0),sK1) | spl2_31),
% 1.54/0.56    inference(superposition,[],[f742,f47])).
% 1.54/0.56  fof(f47,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f27])).
% 1.54/0.56  fof(f27,plain,(
% 1.54/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f6])).
% 1.54/0.56  fof(f6,axiom,(
% 1.54/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.54/0.56  fof(f742,plain,(
% 1.54/0.56    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | spl2_31),
% 1.54/0.56    inference(avatar_component_clause,[],[f740])).
% 1.54/0.56  fof(f740,plain,(
% 1.54/0.56    spl2_31 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 1.54/0.56  fof(f743,plain,(
% 1.54/0.56    ~spl2_31 | ~spl2_15 | spl2_24),
% 1.54/0.56    inference(avatar_split_clause,[],[f738,f656,f335,f740])).
% 1.54/0.56  fof(f656,plain,(
% 1.54/0.56    spl2_24 <=> sK1 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.54/0.56  fof(f738,plain,(
% 1.54/0.56    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | (~spl2_15 | spl2_24)),
% 1.54/0.56    inference(subsumption_resolution,[],[f737,f336])).
% 1.54/0.56  fof(f737,plain,(
% 1.54/0.56    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | ~r1_tarski(k1_tarski(sK0),sK1) | spl2_24),
% 1.54/0.56    inference(superposition,[],[f658,f170])).
% 1.54/0.56  fof(f170,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),X0) | ~r1_tarski(X0,X1)) )),
% 1.54/0.56    inference(superposition,[],[f51,f63])).
% 1.54/0.56  fof(f63,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f30])).
% 1.54/0.56  fof(f30,plain,(
% 1.54/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f8])).
% 1.54/0.56  fof(f8,axiom,(
% 1.54/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.54/0.56  fof(f51,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f11])).
% 1.54/0.56  fof(f11,axiom,(
% 1.54/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.54/0.56  fof(f658,plain,(
% 1.54/0.56    sK1 != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)) | spl2_24),
% 1.54/0.56    inference(avatar_component_clause,[],[f656])).
% 1.54/0.56  fof(f659,plain,(
% 1.54/0.56    ~spl2_24 | spl2_11 | ~spl2_15),
% 1.54/0.56    inference(avatar_split_clause,[],[f654,f335,f273,f656])).
% 1.54/0.56  fof(f273,plain,(
% 1.54/0.56    spl2_11 <=> sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.54/0.56  fof(f654,plain,(
% 1.54/0.56    sK1 != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)) | (spl2_11 | ~spl2_15)),
% 1.54/0.56    inference(subsumption_resolution,[],[f625,f336])).
% 1.54/0.56  fof(f625,plain,(
% 1.54/0.56    sK1 != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)) | ~r1_tarski(k1_tarski(sK0),sK1) | spl2_11),
% 1.54/0.56    inference(superposition,[],[f275,f603])).
% 1.54/0.56  fof(f603,plain,(
% 1.54/0.56    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k4_xboole_0(X3,X2) | ~r1_tarski(X2,X3)) )),
% 1.54/0.56    inference(backward_demodulation,[],[f157,f595])).
% 1.54/0.56  fof(f595,plain,(
% 1.54/0.56    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.54/0.56    inference(forward_demodulation,[],[f588,f181])).
% 1.54/0.56  fof(f181,plain,(
% 1.54/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.56    inference(forward_demodulation,[],[f180,f53])).
% 1.54/0.56  fof(f53,plain,(
% 1.54/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f7])).
% 1.54/0.56  fof(f7,axiom,(
% 1.54/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.54/0.56  fof(f180,plain,(
% 1.54/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f179,f57])).
% 1.54/0.56  fof(f57,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f5])).
% 1.54/0.56  fof(f5,axiom,(
% 1.54/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.56  fof(f179,plain,(
% 1.54/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 1.54/0.56    inference(superposition,[],[f51,f155])).
% 1.54/0.56  fof(f155,plain,(
% 1.54/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.56    inference(forward_demodulation,[],[f149,f53])).
% 1.54/0.56  fof(f149,plain,(
% 1.54/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 1.54/0.56    inference(superposition,[],[f49,f146])).
% 1.54/0.56  fof(f146,plain,(
% 1.54/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.54/0.56    inference(resolution,[],[f83,f58])).
% 1.54/0.56  fof(f58,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f9])).
% 1.54/0.56  fof(f9,axiom,(
% 1.54/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.54/0.56  fof(f83,plain,(
% 1.54/0.56    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 1.54/0.56    inference(superposition,[],[f47,f53])).
% 1.54/0.56  fof(f49,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f12])).
% 1.54/0.56  fof(f12,axiom,(
% 1.54/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.54/0.56  fof(f588,plain,(
% 1.54/0.56    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X1)) )),
% 1.54/0.56    inference(superposition,[],[f457,f49])).
% 1.54/0.56  fof(f457,plain,(
% 1.54/0.56    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.54/0.56    inference(forward_demodulation,[],[f456,f50])).
% 1.54/0.56  fof(f50,plain,(
% 1.54/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f24])).
% 1.54/0.56  fof(f24,plain,(
% 1.54/0.56    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.54/0.56    inference(rectify,[],[f2])).
% 1.54/0.56  fof(f2,axiom,(
% 1.54/0.56    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.54/0.56  fof(f456,plain,(
% 1.54/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f447,f68])).
% 1.54/0.56  fof(f68,plain,(
% 1.54/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.54/0.56    inference(equality_resolution,[],[f45])).
% 1.54/0.56  fof(f45,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.54/0.56    inference(cnf_transformation,[],[f36])).
% 1.54/0.56  fof(f36,plain,(
% 1.54/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.56    inference(flattening,[],[f35])).
% 1.54/0.56  fof(f35,plain,(
% 1.54/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.56    inference(nnf_transformation,[],[f3])).
% 1.54/0.56  fof(f3,axiom,(
% 1.54/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.54/0.56  fof(f447,plain,(
% 1.54/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) | ~r1_tarski(X0,X0)) )),
% 1.54/0.56    inference(superposition,[],[f170,f210])).
% 1.54/0.56  fof(f210,plain,(
% 1.54/0.56    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f195,f68])).
% 1.54/0.56  fof(f195,plain,(
% 1.54/0.56    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1) | ~r1_tarski(X1,X1)) )),
% 1.54/0.56    inference(superposition,[],[f162,f55])).
% 1.54/0.56  fof(f55,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f37])).
% 1.54/0.56  fof(f37,plain,(
% 1.54/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.54/0.56    inference(nnf_transformation,[],[f4])).
% 1.54/0.56  fof(f4,axiom,(
% 1.54/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.54/0.56  fof(f162,plain,(
% 1.54/0.56    ( ! [X2] : (k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)) )),
% 1.54/0.56    inference(superposition,[],[f48,f50])).
% 1.54/0.56  fof(f48,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f1])).
% 1.54/0.56  fof(f1,axiom,(
% 1.54/0.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.54/0.56  fof(f157,plain,(
% 1.54/0.56    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X2)) | ~r1_tarski(X2,X3)) )),
% 1.54/0.56    inference(superposition,[],[f48,f55])).
% 1.54/0.56  fof(f275,plain,(
% 1.54/0.56    sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl2_11),
% 1.54/0.56    inference(avatar_component_clause,[],[f273])).
% 1.54/0.56  fof(f357,plain,(
% 1.54/0.56    ~spl2_2 | spl2_15),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f356])).
% 1.54/0.56  fof(f356,plain,(
% 1.54/0.56    $false | (~spl2_2 | spl2_15)),
% 1.54/0.56    inference(subsumption_resolution,[],[f354,f78])).
% 1.54/0.56  fof(f78,plain,(
% 1.54/0.56    r2_hidden(sK0,sK1) | ~spl2_2),
% 1.54/0.56    inference(avatar_component_clause,[],[f76])).
% 1.54/0.56  fof(f76,plain,(
% 1.54/0.56    spl2_2 <=> r2_hidden(sK0,sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.54/0.56  fof(f354,plain,(
% 1.54/0.56    ~r2_hidden(sK0,sK1) | spl2_15),
% 1.54/0.56    inference(resolution,[],[f337,f60])).
% 1.54/0.56  fof(f60,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f38])).
% 1.54/0.56  fof(f38,plain,(
% 1.54/0.56    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.54/0.56    inference(nnf_transformation,[],[f17])).
% 1.54/0.56  fof(f17,axiom,(
% 1.54/0.56    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.54/0.56  fof(f337,plain,(
% 1.54/0.56    ~r1_tarski(k1_tarski(sK0),sK1) | spl2_15),
% 1.54/0.56    inference(avatar_component_clause,[],[f335])).
% 1.54/0.56  fof(f285,plain,(
% 1.54/0.56    spl2_10),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f284])).
% 1.54/0.56  fof(f284,plain,(
% 1.54/0.56    $false | spl2_10),
% 1.54/0.56    inference(subsumption_resolution,[],[f280,f67])).
% 1.54/0.56  fof(f67,plain,(
% 1.54/0.56    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.54/0.56    inference(equality_resolution,[],[f42])).
% 1.54/0.56  fof(f42,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f34])).
% 1.54/0.56  fof(f34,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.54/0.56    inference(flattening,[],[f33])).
% 1.54/0.56  fof(f33,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.54/0.56    inference(nnf_transformation,[],[f21])).
% 1.54/0.56  fof(f21,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.54/0.56  fof(f280,plain,(
% 1.54/0.56    r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0))) | spl2_10),
% 1.54/0.56    inference(resolution,[],[f271,f61])).
% 1.54/0.56  fof(f61,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f29])).
% 1.54/0.56  fof(f29,plain,(
% 1.54/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f18])).
% 1.54/0.56  fof(f18,axiom,(
% 1.54/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.54/0.56  fof(f271,plain,(
% 1.54/0.56    ~r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | spl2_10),
% 1.54/0.56    inference(avatar_component_clause,[],[f269])).
% 1.54/0.56  fof(f269,plain,(
% 1.54/0.56    spl2_10 <=> r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.54/0.56  fof(f276,plain,(
% 1.54/0.56    ~spl2_10 | ~spl2_11 | spl2_1),
% 1.54/0.56    inference(avatar_split_clause,[],[f261,f71,f273,f269])).
% 1.54/0.56  fof(f71,plain,(
% 1.54/0.56    spl2_1 <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.54/0.56  fof(f261,plain,(
% 1.54/0.56    sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | spl2_1),
% 1.54/0.56    inference(superposition,[],[f73,f143])).
% 1.54/0.56  fof(f143,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.54/0.56    inference(superposition,[],[f49,f56])).
% 1.54/0.56  fof(f56,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f28])).
% 1.54/0.56  fof(f28,plain,(
% 1.54/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f25])).
% 1.54/0.56  fof(f25,plain,(
% 1.54/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.54/0.56    inference(unused_predicate_definition_removal,[],[f10])).
% 1.54/0.56  fof(f10,axiom,(
% 1.54/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.54/0.56  fof(f73,plain,(
% 1.54/0.56    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl2_1),
% 1.54/0.56    inference(avatar_component_clause,[],[f71])).
% 1.54/0.56  fof(f79,plain,(
% 1.54/0.56    spl2_2),
% 1.54/0.56    inference(avatar_split_clause,[],[f39,f76])).
% 1.54/0.56  fof(f39,plain,(
% 1.54/0.56    r2_hidden(sK0,sK1)),
% 1.54/0.56    inference(cnf_transformation,[],[f32])).
% 1.54/0.56  fof(f32,plain,(
% 1.54/0.56    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f31])).
% 1.54/0.56  fof(f31,plain,(
% 1.54/0.56    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f26,plain,(
% 1.54/0.56    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f23])).
% 1.54/0.56  fof(f23,negated_conjecture,(
% 1.54/0.56    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.54/0.56    inference(negated_conjecture,[],[f22])).
% 1.54/0.56  fof(f22,conjecture,(
% 1.54/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 1.54/0.56  fof(f74,plain,(
% 1.54/0.56    ~spl2_1),
% 1.54/0.56    inference(avatar_split_clause,[],[f40,f71])).
% 1.54/0.56  fof(f40,plain,(
% 1.54/0.56    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.54/0.56    inference(cnf_transformation,[],[f32])).
% 1.54/0.56  % SZS output end Proof for theBenchmark
% 1.54/0.56  % (18779)------------------------------
% 1.54/0.56  % (18779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (18779)Termination reason: Refutation
% 1.54/0.56  
% 1.54/0.56  % (18779)Memory used [KB]: 6652
% 1.54/0.56  % (18764)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.54/0.56  % (18779)Time elapsed: 0.144 s
% 1.54/0.56  % (18779)------------------------------
% 1.54/0.56  % (18779)------------------------------
% 1.54/0.56  % (18782)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.54/0.57  % (18757)Success in time 0.203 s
%------------------------------------------------------------------------------
