%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:30 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 150 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  266 ( 578 expanded)
%              Number of equality atoms :  179 ( 475 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f276,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f93,f103,f113,f118,f123,f131,f133,f162,f275])).

fof(f275,plain,
    ( spl3_2
    | spl3_4
    | spl3_6
    | spl3_8
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl3_2
    | spl3_4
    | spl3_6
    | spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f273,f82])).

fof(f82,plain,
    ( sK0 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_2
  <=> sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f273,plain,
    ( sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | spl3_4
    | spl3_6
    | spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f272,f112])).

fof(f112,plain,
    ( k1_xboole_0 != sK0
    | spl3_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f272,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | spl3_4
    | spl3_6
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f271,f102])).

fof(f102,plain,
    ( sK0 != k1_tarski(sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_6
  <=> sK0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f271,plain,
    ( sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f264,f92])).

fof(f92,plain,
    ( sK0 != k1_tarski(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_4
  <=> sK0 = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f264,plain,
    ( sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | ~ spl3_9 ),
    inference(resolution,[],[f67,f165])).

fof(f165,plain,
    ( r1_tarski(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ spl3_9 ),
    inference(superposition,[],[f46,f117])).

fof(f117,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_9
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = X0 ) ),
    inference(definition_unfolding,[],[f53,f42,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

% (7136)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f162,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl3_7 ),
    inference(trivial_inequality_removal,[],[f158])).

fof(f158,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_7 ),
    inference(superposition,[],[f108,f154])).

fof(f154,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f108,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_7
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f133,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f98,f40])).

fof(f40,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f98,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,k1_tarski(sK2)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f131,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f125,f40])).

fof(f125,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,k1_tarski(sK1)))
    | spl3_3 ),
    inference(backward_demodulation,[],[f88,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f88,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_3
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f123,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f121])).

fof(f121,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_1 ),
    inference(superposition,[],[f78,f119])).

fof(f119,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f40,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f78,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f118,plain,
    ( spl3_9
    | spl3_8
    | spl3_6
    | spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f62,f80,f90,f100,f110,f115])).

fof(f62,plain,
    ( sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f32,f42,f42])).

fof(f32,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ( sK0 != k2_tarski(sK1,sK2)
        & sK0 != k1_tarski(sK2)
        & sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
    & ( sK0 = k2_tarski(sK1,sK2)
      | sK0 = k1_tarski(sK2)
      | sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( sK0 != k2_tarski(sK1,sK2)
          & sK0 != k1_tarski(sK2)
          & sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
      & ( sK0 = k2_tarski(sK1,sK2)
        | sK0 = k1_tarski(sK2)
        | sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f113,plain,
    ( ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f104,f110,f106])).

fof(f104,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(inner_rewriting,[],[f61])).

fof(f61,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f33,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

% (7109)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (7136)Refutation not found, incomplete strategy% (7136)------------------------------
% (7136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f103,plain,
    ( ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f94,f100,f96])).

fof(f94,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,k1_tarski(sK2))) ),
    inference(inner_rewriting,[],[f60])).

fof(f60,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f34,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f93,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f84,f90,f86])).

fof(f84,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),sK0)) ),
    inference(inner_rewriting,[],[f59])).

fof(f59,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f35,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f74,f80,f76])).

fof(f74,plain,
    ( sK0 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 != k4_xboole_0(sK0,sK0) ),
    inference(inner_rewriting,[],[f58])).

fof(f58,plain,
    ( sK0 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f36,f42,f42])).

fof(f36,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:24:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (7135)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (7112)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.50  % (7127)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (7131)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (7135)Refutation not found, incomplete strategy% (7135)------------------------------
% 0.21/0.51  % (7135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7135)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7135)Memory used [KB]: 6268
% 0.21/0.51  % (7135)Time elapsed: 0.112 s
% 0.21/0.51  % (7135)------------------------------
% 0.21/0.51  % (7135)------------------------------
% 0.21/0.51  % (7123)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.20/0.52  % (7113)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.20/0.52  % (7117)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.20/0.52  % (7111)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.20/0.52  % (7115)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.52  % (7120)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.20/0.53  % (7126)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.20/0.53  % (7116)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.20/0.53  % (7128)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.20/0.53  % (7118)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.20/0.53  % (7119)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.20/0.53  % (7114)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.20/0.53  % (7133)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.20/0.53  % (7115)Refutation found. Thanks to Tanya!
% 1.20/0.53  % SZS status Theorem for theBenchmark
% 1.20/0.53  % SZS output start Proof for theBenchmark
% 1.20/0.53  fof(f276,plain,(
% 1.20/0.53    $false),
% 1.20/0.53    inference(avatar_sat_refutation,[],[f83,f93,f103,f113,f118,f123,f131,f133,f162,f275])).
% 1.20/0.53  fof(f275,plain,(
% 1.20/0.53    spl3_2 | spl3_4 | spl3_6 | spl3_8 | ~spl3_9),
% 1.20/0.53    inference(avatar_contradiction_clause,[],[f274])).
% 1.20/0.53  fof(f274,plain,(
% 1.20/0.53    $false | (spl3_2 | spl3_4 | spl3_6 | spl3_8 | ~spl3_9)),
% 1.20/0.53    inference(subsumption_resolution,[],[f273,f82])).
% 1.20/0.53  fof(f82,plain,(
% 1.20/0.53    sK0 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | spl3_2),
% 1.20/0.53    inference(avatar_component_clause,[],[f80])).
% 1.20/0.53  fof(f80,plain,(
% 1.20/0.53    spl3_2 <=> sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.20/0.53  fof(f273,plain,(
% 1.20/0.53    sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | (spl3_4 | spl3_6 | spl3_8 | ~spl3_9)),
% 1.20/0.53    inference(subsumption_resolution,[],[f272,f112])).
% 1.20/0.53  fof(f112,plain,(
% 1.20/0.53    k1_xboole_0 != sK0 | spl3_8),
% 1.20/0.53    inference(avatar_component_clause,[],[f110])).
% 1.20/0.53  fof(f110,plain,(
% 1.20/0.53    spl3_8 <=> k1_xboole_0 = sK0),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.20/0.53  fof(f272,plain,(
% 1.20/0.53    k1_xboole_0 = sK0 | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | (spl3_4 | spl3_6 | ~spl3_9)),
% 1.20/0.53    inference(subsumption_resolution,[],[f271,f102])).
% 1.20/0.53  fof(f102,plain,(
% 1.20/0.53    sK0 != k1_tarski(sK1) | spl3_6),
% 1.20/0.53    inference(avatar_component_clause,[],[f100])).
% 1.20/0.53  fof(f100,plain,(
% 1.20/0.53    spl3_6 <=> sK0 = k1_tarski(sK1)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.20/0.53  fof(f271,plain,(
% 1.20/0.53    sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | (spl3_4 | ~spl3_9)),
% 1.20/0.53    inference(subsumption_resolution,[],[f264,f92])).
% 1.20/0.53  fof(f92,plain,(
% 1.20/0.53    sK0 != k1_tarski(sK2) | spl3_4),
% 1.20/0.53    inference(avatar_component_clause,[],[f90])).
% 1.20/0.53  fof(f90,plain,(
% 1.20/0.53    spl3_4 <=> sK0 = k1_tarski(sK2)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.20/0.53  fof(f264,plain,(
% 1.20/0.53    sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | ~spl3_9),
% 1.20/0.53    inference(resolution,[],[f67,f165])).
% 1.20/0.53  fof(f165,plain,(
% 1.20/0.53    r1_tarski(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | ~spl3_9),
% 1.20/0.53    inference(trivial_inequality_removal,[],[f164])).
% 1.20/0.53  fof(f164,plain,(
% 1.20/0.53    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | ~spl3_9),
% 1.20/0.53    inference(superposition,[],[f46,f117])).
% 1.20/0.53  fof(f117,plain,(
% 1.20/0.53    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | ~spl3_9),
% 1.20/0.53    inference(avatar_component_clause,[],[f115])).
% 1.20/0.53  fof(f115,plain,(
% 1.20/0.53    spl3_9 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.20/0.53  fof(f46,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f28])).
% 1.20/0.53  fof(f28,plain,(
% 1.20/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.20/0.53    inference(nnf_transformation,[],[f4])).
% 1.20/0.53  fof(f4,axiom,(
% 1.20/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.20/0.54  fof(f67,plain,(
% 1.20/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = X0) )),
% 1.20/0.54    inference(definition_unfolding,[],[f53,f42,f42])).
% 1.20/0.54  fof(f42,plain,(
% 1.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.20/0.54    inference(cnf_transformation,[],[f12])).
% 1.20/0.54  fof(f12,axiom,(
% 1.20/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.20/0.54  fof(f53,plain,(
% 1.20/0.54    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.20/0.54    inference(cnf_transformation,[],[f31])).
% 1.20/0.54  fof(f31,plain,(
% 1.20/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.20/0.54    inference(flattening,[],[f30])).
% 1.20/0.54  fof(f30,plain,(
% 1.20/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.20/0.54    inference(nnf_transformation,[],[f21])).
% 1.20/0.54  fof(f21,plain,(
% 1.20/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.20/0.54    inference(ennf_transformation,[],[f13])).
% 1.20/0.54  fof(f13,axiom,(
% 1.20/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.20/0.54  % (7136)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.20/0.54  fof(f162,plain,(
% 1.20/0.54    spl3_7),
% 1.20/0.54    inference(avatar_contradiction_clause,[],[f161])).
% 1.20/0.54  fof(f161,plain,(
% 1.20/0.54    $false | spl3_7),
% 1.20/0.54    inference(trivial_inequality_removal,[],[f158])).
% 1.20/0.54  fof(f158,plain,(
% 1.20/0.54    k1_xboole_0 != k1_xboole_0 | spl3_7),
% 1.20/0.54    inference(superposition,[],[f108,f154])).
% 1.20/0.54  fof(f154,plain,(
% 1.20/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.20/0.54    inference(resolution,[],[f47,f37])).
% 1.20/0.54  fof(f37,plain,(
% 1.20/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.20/0.54    inference(cnf_transformation,[],[f6])).
% 1.20/0.54  fof(f6,axiom,(
% 1.20/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.20/0.54  fof(f47,plain,(
% 1.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.20/0.54    inference(cnf_transformation,[],[f28])).
% 1.20/0.54  fof(f108,plain,(
% 1.20/0.54    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) | spl3_7),
% 1.20/0.54    inference(avatar_component_clause,[],[f106])).
% 1.20/0.54  fof(f106,plain,(
% 1.20/0.54    spl3_7 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.20/0.54  fof(f133,plain,(
% 1.20/0.54    spl3_5),
% 1.20/0.54    inference(avatar_contradiction_clause,[],[f132])).
% 1.20/0.54  fof(f132,plain,(
% 1.20/0.54    $false | spl3_5),
% 1.20/0.54    inference(subsumption_resolution,[],[f98,f40])).
% 1.20/0.54  fof(f40,plain,(
% 1.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.20/0.54    inference(cnf_transformation,[],[f10])).
% 1.20/0.54  fof(f10,axiom,(
% 1.20/0.54    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.20/0.54  fof(f98,plain,(
% 1.20/0.54    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,k1_tarski(sK2))) | spl3_5),
% 1.20/0.54    inference(avatar_component_clause,[],[f96])).
% 1.20/0.54  fof(f96,plain,(
% 1.20/0.54    spl3_5 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,k1_tarski(sK2)))),
% 1.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.20/0.54  fof(f131,plain,(
% 1.20/0.54    spl3_3),
% 1.20/0.54    inference(avatar_contradiction_clause,[],[f130])).
% 1.20/0.54  fof(f130,plain,(
% 1.20/0.54    $false | spl3_3),
% 1.20/0.54    inference(subsumption_resolution,[],[f125,f40])).
% 1.20/0.54  fof(f125,plain,(
% 1.20/0.54    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,k1_tarski(sK1))) | spl3_3),
% 1.20/0.54    inference(backward_demodulation,[],[f88,f41])).
% 1.20/0.54  fof(f41,plain,(
% 1.20/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.20/0.54    inference(cnf_transformation,[],[f1])).
% 1.20/0.54  fof(f1,axiom,(
% 1.20/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.20/0.54  fof(f88,plain,(
% 1.20/0.54    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),sK0)) | spl3_3),
% 1.20/0.54    inference(avatar_component_clause,[],[f86])).
% 1.20/0.54  fof(f86,plain,(
% 1.20/0.54    spl3_3 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),sK0))),
% 1.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.20/0.54  fof(f123,plain,(
% 1.20/0.54    spl3_1),
% 1.20/0.54    inference(avatar_contradiction_clause,[],[f122])).
% 1.20/0.54  fof(f122,plain,(
% 1.20/0.54    $false | spl3_1),
% 1.20/0.54    inference(trivial_inequality_removal,[],[f121])).
% 1.20/0.54  fof(f121,plain,(
% 1.20/0.54    k1_xboole_0 != k1_xboole_0 | spl3_1),
% 1.20/0.54    inference(superposition,[],[f78,f119])).
% 1.20/0.54  fof(f119,plain,(
% 1.20/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.20/0.54    inference(superposition,[],[f40,f39])).
% 1.20/0.54  fof(f39,plain,(
% 1.20/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.20/0.54    inference(cnf_transformation,[],[f16])).
% 1.20/0.54  fof(f16,plain,(
% 1.20/0.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.20/0.54    inference(rectify,[],[f2])).
% 1.20/0.54  fof(f2,axiom,(
% 1.20/0.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.20/0.54  fof(f78,plain,(
% 1.20/0.54    k1_xboole_0 != k4_xboole_0(sK0,sK0) | spl3_1),
% 1.20/0.54    inference(avatar_component_clause,[],[f76])).
% 1.20/0.54  fof(f76,plain,(
% 1.20/0.54    spl3_1 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 1.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.20/0.54  fof(f118,plain,(
% 1.20/0.54    spl3_9 | spl3_8 | spl3_6 | spl3_4 | spl3_2),
% 1.20/0.54    inference(avatar_split_clause,[],[f62,f80,f90,f100,f110,f115])).
% 1.20/0.54  fof(f62,plain,(
% 1.20/0.54    sK0 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.20/0.54    inference(definition_unfolding,[],[f32,f42,f42])).
% 1.20/0.54  fof(f32,plain,(
% 1.20/0.54    sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.20/0.54    inference(cnf_transformation,[],[f25])).
% 1.20/0.54  fof(f25,plain,(
% 1.20/0.54    ((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)))),
% 1.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).
% 1.20/0.54  fof(f24,plain,(
% 1.20/0.54    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)))) => (((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))))),
% 1.20/0.54    introduced(choice_axiom,[])).
% 1.20/0.54  fof(f23,plain,(
% 1.20/0.54    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 1.20/0.54    inference(flattening,[],[f22])).
% 1.20/0.54  fof(f22,plain,(
% 1.20/0.54    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 1.20/0.54    inference(nnf_transformation,[],[f17])).
% 1.20/0.54  fof(f17,plain,(
% 1.20/0.54    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.20/0.54    inference(ennf_transformation,[],[f15])).
% 1.20/0.54  fof(f15,negated_conjecture,(
% 1.20/0.54    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.20/0.54    inference(negated_conjecture,[],[f14])).
% 1.20/0.54  fof(f14,conjecture,(
% 1.20/0.54    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 1.20/0.54  fof(f113,plain,(
% 1.20/0.54    ~spl3_7 | ~spl3_8),
% 1.20/0.54    inference(avatar_split_clause,[],[f104,f110,f106])).
% 1.20/0.54  fof(f104,plain,(
% 1.20/0.54    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.20/0.54    inference(inner_rewriting,[],[f61])).
% 1.20/0.54  fof(f61,plain,(
% 1.20/0.54    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.20/0.54    inference(definition_unfolding,[],[f33,f42])).
% 1.20/0.54  fof(f33,plain,(
% 1.20/0.54    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.20/0.54    inference(cnf_transformation,[],[f25])).
% 1.20/0.54  % (7109)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.20/0.54  % (7136)Refutation not found, incomplete strategy% (7136)------------------------------
% 1.20/0.54  % (7136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  fof(f103,plain,(
% 1.37/0.54    ~spl3_5 | ~spl3_6),
% 1.37/0.54    inference(avatar_split_clause,[],[f94,f100,f96])).
% 1.37/0.54  fof(f94,plain,(
% 1.37/0.54    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,k1_tarski(sK2)))),
% 1.37/0.54    inference(inner_rewriting,[],[f60])).
% 1.37/0.54  fof(f60,plain,(
% 1.37/0.54    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.37/0.54    inference(definition_unfolding,[],[f34,f42])).
% 1.37/0.54  fof(f34,plain,(
% 1.37/0.54    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.37/0.54    inference(cnf_transformation,[],[f25])).
% 1.37/0.54  fof(f93,plain,(
% 1.37/0.54    ~spl3_3 | ~spl3_4),
% 1.37/0.54    inference(avatar_split_clause,[],[f84,f90,f86])).
% 1.37/0.54  fof(f84,plain,(
% 1.37/0.54    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),sK0))),
% 1.37/0.54    inference(inner_rewriting,[],[f59])).
% 1.37/0.54  fof(f59,plain,(
% 1.37/0.54    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.37/0.54    inference(definition_unfolding,[],[f35,f42])).
% 1.37/0.54  fof(f35,plain,(
% 1.37/0.54    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.37/0.54    inference(cnf_transformation,[],[f25])).
% 1.37/0.54  fof(f83,plain,(
% 1.37/0.54    ~spl3_1 | ~spl3_2),
% 1.37/0.54    inference(avatar_split_clause,[],[f74,f80,f76])).
% 1.37/0.54  fof(f74,plain,(
% 1.37/0.54    sK0 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | k1_xboole_0 != k4_xboole_0(sK0,sK0)),
% 1.37/0.54    inference(inner_rewriting,[],[f58])).
% 1.37/0.54  fof(f58,plain,(
% 1.37/0.54    sK0 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) | k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 1.37/0.54    inference(definition_unfolding,[],[f36,f42,f42])).
% 1.37/0.54  fof(f36,plain,(
% 1.37/0.54    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.37/0.54    inference(cnf_transformation,[],[f25])).
% 1.37/0.54  % SZS output end Proof for theBenchmark
% 1.37/0.54  % (7115)------------------------------
% 1.37/0.54  % (7115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (7115)Termination reason: Refutation
% 1.37/0.54  
% 1.37/0.54  % (7115)Memory used [KB]: 10746
% 1.37/0.54  % (7115)Time elapsed: 0.081 s
% 1.37/0.54  % (7115)------------------------------
% 1.37/0.54  % (7115)------------------------------
% 1.37/0.54  % (7137)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.37/0.54  % (7107)Success in time 0.176 s
%------------------------------------------------------------------------------
