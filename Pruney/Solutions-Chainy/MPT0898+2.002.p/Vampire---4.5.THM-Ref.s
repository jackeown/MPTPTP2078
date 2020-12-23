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
% DateTime   : Thu Dec  3 12:59:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 131 expanded)
%              Number of leaves         :   17 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  212 ( 376 expanded)
%              Number of equality atoms :  105 ( 202 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f74,f84,f93,f106,f118,f123,f140,f193,f203])).

fof(f203,plain,
    ( spl2_10
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl2_10
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f139,f38,f192])).

fof(f192,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),k2_zfmisc_1(X6,X7))
        | r1_tarski(sK1,X7) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl2_15
  <=> ! [X7,X6] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),k2_zfmisc_1(X6,X7))
        | r1_tarski(sK1,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f139,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl2_10
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f193,plain,
    ( spl2_5
    | spl2_15
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f58,f51,f191,f71])).

fof(f71,plain,
    ( spl2_5
  <=> k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f51,plain,
    ( spl2_2
  <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f58,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),k2_zfmisc_1(X6,X7))
        | k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0)
        | r1_tarski(sK1,X7) )
    | ~ spl2_2 ),
    inference(superposition,[],[f35,f53])).

fof(f53,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f140,plain,
    ( ~ spl2_10
    | spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f134,f81,f46,f137])).

fof(f46,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f81,plain,
    ( spl2_6
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f134,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f83,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f123,plain,
    ( spl2_7
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl2_7
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f92,f92,f92,f105,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f105,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_8
  <=> k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f92,plain,
    ( k1_xboole_0 != sK0
    | spl2_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl2_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f118,plain,
    ( spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f114,f67,f63])).

fof(f63,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f67,plain,
    ( spl2_4
  <=> k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | ~ spl2_4 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | ~ spl2_4 ),
    inference(superposition,[],[f28,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f106,plain,
    ( spl2_7
    | spl2_8
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f100,f71,f103,f90])).

fof(f100,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0)
    | k1_xboole_0 = sK0
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0)
    | k1_xboole_0 = sK0
    | ~ spl2_5 ),
    inference(superposition,[],[f25,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f93,plain,
    ( ~ spl2_7
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f87,f63,f46,f90])).

fof(f87,plain,
    ( k1_xboole_0 != sK0
    | spl2_1
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f48,f65])).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f48,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f84,plain,
    ( spl2_6
    | spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f75,f51,f71,f81])).

fof(f75,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0)
    | r1_tarski(sK0,sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f57,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0))
        | k1_xboole_0 = k2_zfmisc_1(X4,X5)
        | r1_tarski(X5,sK1) )
    | ~ spl2_2 ),
    inference(superposition,[],[f35,f53])).

fof(f74,plain,
    ( spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f60,f51,f71,f67,f63])).

fof(f60,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0)
    | k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1)
    | k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(superposition,[],[f25,f53])).

fof(f54,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f36,f51])).

fof(f36,plain,(
    k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1) ),
    inference(definition_unfolding,[],[f20,f32,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f20,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != sK1
    & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) )
   => ( sK0 != sK1
      & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f49,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f46])).

fof(f21,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:44:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (2684)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (2676)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (2692)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (2684)Refutation not found, incomplete strategy% (2684)------------------------------
% 0.21/0.51  % (2684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2670)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (2676)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (2684)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2684)Memory used [KB]: 1663
% 0.21/0.52  % (2684)Time elapsed: 0.104 s
% 0.21/0.52  % (2684)------------------------------
% 0.21/0.52  % (2684)------------------------------
% 0.21/0.52  % (2678)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (2671)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (2678)Refutation not found, incomplete strategy% (2678)------------------------------
% 0.21/0.52  % (2678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2678)Memory used [KB]: 10618
% 0.21/0.52  % (2678)Time elapsed: 0.115 s
% 0.21/0.52  % (2678)------------------------------
% 0.21/0.52  % (2678)------------------------------
% 0.21/0.52  % (2692)Refutation not found, incomplete strategy% (2692)------------------------------
% 0.21/0.52  % (2692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2692)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2692)Memory used [KB]: 6140
% 0.21/0.52  % (2692)Time elapsed: 0.116 s
% 0.21/0.52  % (2692)------------------------------
% 0.21/0.52  % (2692)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f49,f54,f74,f84,f93,f106,f118,f123,f140,f193,f203])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    spl2_10 | ~spl2_15),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f195])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    $false | (spl2_10 | ~spl2_15)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f139,f38,f192])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ( ! [X6,X7] : (~r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),k2_zfmisc_1(X6,X7)) | r1_tarski(sK1,X7)) ) | ~spl2_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f191])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    spl2_15 <=> ! [X7,X6] : (~r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),k2_zfmisc_1(X6,X7)) | r1_tarski(sK1,X7))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ~r1_tarski(sK1,sK0) | spl2_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl2_10 <=> r1_tarski(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    spl2_5 | spl2_15 | ~spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f58,f51,f191,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl2_5 <=> k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl2_2 <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X6,X7] : (~r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),k2_zfmisc_1(X6,X7)) | k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) | r1_tarski(sK1,X7)) ) | ~spl2_2),
% 0.21/0.52    inference(superposition,[],[f35,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1) | ~spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X1,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ~spl2_10 | spl2_1 | ~spl2_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f134,f81,f46,f137])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    spl2_1 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl2_6 <=> r1_tarski(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    sK0 = sK1 | ~r1_tarski(sK1,sK0) | ~spl2_6),
% 0.21/0.52    inference(resolution,[],[f83,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    r1_tarski(sK0,sK1) | ~spl2_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f81])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    spl2_7 | ~spl2_8),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    $false | (spl2_7 | ~spl2_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f92,f92,f92,f105,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0) | ~spl2_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl2_8 <=> k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | spl2_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl2_7 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl2_3 | ~spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f114,f67,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl2_3 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl2_4 <=> k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl2_4),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | ~spl2_4),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | ~spl2_4),
% 0.21/0.52    inference(superposition,[],[f28,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1) | ~spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f67])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl2_7 | spl2_8 | ~spl2_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f100,f71,f103,f90])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0) | k1_xboole_0 = sK0 | ~spl2_5),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0) | k1_xboole_0 = sK0 | ~spl2_5),
% 0.21/0.52    inference(superposition,[],[f25,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) | ~spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ~spl2_7 | spl2_1 | ~spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f87,f63,f46,f90])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | (spl2_1 | ~spl2_3)),
% 0.21/0.52    inference(backward_demodulation,[],[f48,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    sK0 != sK1 | spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f46])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl2_6 | spl2_5 | ~spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f75,f51,f71,f81])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) | r1_tarski(sK0,sK1) | ~spl2_2),
% 0.21/0.52    inference(resolution,[],[f57,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0)) | k1_xboole_0 = k2_zfmisc_1(X4,X5) | r1_tarski(X5,sK1)) ) | ~spl2_2),
% 0.21/0.52    inference(superposition,[],[f35,f53])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl2_3 | spl2_4 | ~spl2_5 | ~spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f60,f51,f71,f67,f63])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) | k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1) | k1_xboole_0 = sK1 | ~spl2_2),
% 0.21/0.52    inference(superposition,[],[f25,f53])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f51])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f32,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)) => (sK0 != sK1 & k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ~spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f21,f46])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    sK0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (2676)------------------------------
% 0.21/0.52  % (2676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2676)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (2676)Memory used [KB]: 10746
% 0.21/0.52  % (2676)Time elapsed: 0.111 s
% 0.21/0.52  % (2676)------------------------------
% 0.21/0.52  % (2676)------------------------------
% 0.21/0.52  % (2665)Success in time 0.164 s
%------------------------------------------------------------------------------
