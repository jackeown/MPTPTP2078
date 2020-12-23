%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 126 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :  210 ( 358 expanded)
%              Number of equality atoms :   50 (  81 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f44,f48,f52,f67,f78,f96,f100,f112,f116,f127,f132])).

fof(f132,plain,
    ( spl4_8
    | spl4_7
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f131,f125,f73,f76])).

fof(f76,plain,
    ( spl4_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f73,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f125,plain,
    ( spl4_14
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f131,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl4_14 ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl4_14 ),
    inference(superposition,[],[f26,f126])).

fof(f126,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f127,plain,
    ( spl4_14
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f119,f39,f35,f125])).

fof(f35,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f39,plain,
    ( spl4_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f119,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f58,f40])).

fof(f40,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))
        | k1_xboole_0 = k2_zfmisc_1(X0,sK1) )
    | spl4_1 ),
    inference(resolution,[],[f30,f36])).

fof(f36,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f116,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f111,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f111,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_13
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f112,plain,
    ( ~ spl4_13
    | spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f107,f76,f35,f110])).

fof(f107,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl4_1
    | ~ spl4_8 ),
    inference(superposition,[],[f36,f77])).

fof(f77,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f100,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl4_11 ),
    inference(resolution,[],[f95,f22])).

fof(f95,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_11
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f96,plain,
    ( ~ spl4_11
    | spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f92,f73,f50,f46,f94])).

fof(f46,plain,
    ( spl4_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f50,plain,
    ( spl4_5
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f92,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(resolution,[],[f83,f51])).

fof(f51,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | spl4_4
    | ~ spl4_7 ),
    inference(superposition,[],[f54,f74])).

fof(f74,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f54,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK0,X0)
        | ~ r1_tarski(sK0,X0) )
    | spl4_4 ),
    inference(resolution,[],[f25,f47])).

fof(f47,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f78,plain,
    ( spl4_7
    | spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f71,f65,f76,f73])).

fof(f65,plain,
    ( spl4_6
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f71,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_6 ),
    inference(superposition,[],[f26,f66])).

fof(f66,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f67,plain,
    ( spl4_6
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f59,f42,f35,f65])).

fof(f42,plain,
    ( spl4_3
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f59,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f57,f43])).

fof(f43,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1))
        | k1_xboole_0 = k2_zfmisc_1(sK1,X0) )
    | spl4_1 ),
    inference(resolution,[],[f29,f36])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X2)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f31,f50])).

fof(f31,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f48,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK1,sK3)
    & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) )
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r1_tarski(X1,X3)
            & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3,X2,X1] :
        ( ~ r1_tarski(X1,X3)
        & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
          | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
   => ( ~ r1_tarski(sK1,sK3)
      & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
        | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f44,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f20,f42,f39])).

fof(f20,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f35])).

fof(f21,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:38:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (10492)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (10490)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (10490)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f37,f44,f48,f52,f67,f78,f96,f100,f112,f116,f127,f132])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl4_8 | spl4_7 | ~spl4_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f131,f125,f73,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl4_8 <=> k1_xboole_0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl4_7 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    spl4_14 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl4_14),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f130])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl4_14),
% 0.21/0.47    inference(superposition,[],[f26,f126])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f125])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl4_14 | spl4_1 | ~spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f119,f39,f35,f125])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl4_1 <=> r1_tarski(sK1,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl4_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (spl4_1 | ~spl4_2)),
% 0.21/0.47    inference(resolution,[],[f58,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f39])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) | k1_xboole_0 = k2_zfmisc_1(X0,sK1)) ) | spl4_1),
% 0.21/0.47    inference(resolution,[],[f30,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ~r1_tarski(sK1,sK3) | spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f35])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    spl4_13),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f113])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    $false | spl4_13),
% 0.21/0.47    inference(resolution,[],[f111,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ~r1_tarski(k1_xboole_0,sK3) | spl4_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f110])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl4_13 <=> r1_tarski(k1_xboole_0,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ~spl4_13 | spl4_1 | ~spl4_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f107,f76,f35,f110])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ~r1_tarski(k1_xboole_0,sK3) | (spl4_1 | ~spl4_8)),
% 0.21/0.47    inference(superposition,[],[f36,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | ~spl4_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f76])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl4_11),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f97])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    $false | spl4_11),
% 0.21/0.47    inference(resolution,[],[f95,f22])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl4_11 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ~spl4_11 | spl4_4 | ~spl4_5 | ~spl4_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f92,f73,f50,f46,f94])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl4_4 <=> v1_xboole_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl4_5 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.21/0.47    inference(resolution,[],[f83,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,X0)) ) | (spl4_4 | ~spl4_7)),
% 0.21/0.47    inference(superposition,[],[f54,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl4_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_xboole_0(sK0,X0) | ~r1_tarski(sK0,X0)) ) | spl4_4),
% 0.21/0.47    inference(resolution,[],[f25,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ~v1_xboole_0(sK0) | spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl4_7 | spl4_8 | ~spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f71,f65,f76,f73])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl4_6 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl4_6),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl4_6),
% 0.21/0.47    inference(superposition,[],[f26,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | ~spl4_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f65])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl4_6 | spl4_1 | ~spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f59,f42,f35,f65])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl4_3 <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | (spl4_1 | ~spl4_3)),
% 0.21/0.47    inference(resolution,[],[f57,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | ~spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f42])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)) | k1_xboole_0 = k2_zfmisc_1(sK1,X0)) ) | spl4_1),
% 0.21/0.47    inference(resolution,[],[f29,f36])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (r1_tarski(X0,X2) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl4_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f50])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    inference(equality_resolution,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ~spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f46])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    (~r1_tarski(sK1,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) & ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f15,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0)) => (? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)))) => (~r1_tarski(sK1,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl4_2 | spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f42,f39])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f35])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (10490)------------------------------
% 0.21/0.48  % (10490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10490)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (10490)Memory used [KB]: 10618
% 0.21/0.48  % (10490)Time elapsed: 0.052 s
% 0.21/0.48  % (10490)------------------------------
% 0.21/0.48  % (10490)------------------------------
% 0.21/0.48  % (10483)Success in time 0.116 s
%------------------------------------------------------------------------------
