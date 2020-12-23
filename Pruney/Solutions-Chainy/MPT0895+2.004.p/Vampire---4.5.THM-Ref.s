%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:11 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 166 expanded)
%              Number of leaves         :   12 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  197 ( 409 expanded)
%              Number of equality atoms :  102 ( 269 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f60,f67,f72,f78,f83,f87,f91,f108,f109,f127,f138,f148])).

fof(f148,plain,
    ( ~ spl4_6
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f147,f124,f53,f64])).

fof(f64,plain,
    ( spl4_6
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f53,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f124,plain,
    ( spl4_9
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f147,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(trivial_inequality_removal,[],[f146])).

fof(f146,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f144,f55])).

fof(f55,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f144,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | k1_xboole_0 != sK1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f143,f37])).

fof(f37,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f143,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | k1_xboole_0 != sK1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f33,f126])).

fof(f126,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f33,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f16,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f16,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

% (16990)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f138,plain,
    ( spl4_4
    | spl4_5
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl4_4
    | spl4_5
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f58,f54,f126,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f54,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f58,plain,
    ( k1_xboole_0 != sK0
    | spl4_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f127,plain,
    ( spl4_9
    | spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f118,f105,f48,f124])).

fof(f48,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f105,plain,
    ( spl4_8
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f118,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_8 ),
    inference(trivial_inequality_removal,[],[f111])).

fof(f111,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_8 ),
    inference(superposition,[],[f23,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f109,plain,
    ( ~ spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f34,f43,f57])).

fof(f43,plain,
    ( spl4_2
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f34,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f15,f30])).

fof(f15,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f108,plain,
    ( spl4_8
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f99,f43,f39,f105])).

fof(f39,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f99,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f23,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f91,plain,
    ( ~ spl4_6
    | spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f90,f57,f43,f64])).

fof(f90,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f89,f37])).

fof(f89,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f88,f37])).

fof(f88,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2),sK3)
    | spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f45,f59])).

fof(f59,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f45,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f87,plain,
    ( ~ spl4_6
    | spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f86,f53,f43,f64])).

fof(f86,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f85,f37])).

fof(f85,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f84,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f84,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2),sK3)
    | spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f45,f55])).

fof(f83,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f36,f77])).

fof(f77,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_7
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f78,plain,
    ( ~ spl4_7
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f73,f43,f39,f75])).

fof(f73,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)
    | ~ spl4_1
    | spl4_2 ),
    inference(forward_demodulation,[],[f45,f40])).

fof(f40,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f72,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f37,f66])).

fof(f66,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f67,plain,
    ( ~ spl4_6
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f62,f48,f43,f64])).

fof(f62,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f61,f36])).

fof(f61,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0),sK3)
    | spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f45,f49])).

fof(f49,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f60,plain,
    ( spl4_1
    | spl4_3
    | spl4_4
    | spl4_5
    | spl4_2 ),
    inference(avatar_split_clause,[],[f35,f43,f57,f53,f48,f39])).

fof(f35,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(definition_unfolding,[],[f14,f30])).

fof(f14,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,
    ( ~ spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f32,f43,f48])).

fof(f32,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f17,f30])).

fof(f17,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f31,f43,f39])).

fof(f31,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f18,f30])).

fof(f18,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 11:31:34 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.43  % (16981)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.46  % (17005)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.47  % (17001)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.18/0.47  % (16997)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.18/0.47  % (16992)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.47  % (17001)Refutation found. Thanks to Tanya!
% 0.18/0.47  % SZS status Theorem for theBenchmark
% 0.18/0.48  % SZS output start Proof for theBenchmark
% 0.18/0.48  fof(f149,plain,(
% 0.18/0.48    $false),
% 0.18/0.48    inference(avatar_sat_refutation,[],[f46,f51,f60,f67,f72,f78,f83,f87,f91,f108,f109,f127,f138,f148])).
% 0.18/0.48  fof(f148,plain,(
% 0.18/0.48    ~spl4_6 | ~spl4_4 | ~spl4_9),
% 0.18/0.48    inference(avatar_split_clause,[],[f147,f124,f53,f64])).
% 0.18/0.48  fof(f64,plain,(
% 0.18/0.48    spl4_6 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK3)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.18/0.48  fof(f53,plain,(
% 0.18/0.48    spl4_4 <=> k1_xboole_0 = sK1),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.18/0.48  fof(f124,plain,(
% 0.18/0.48    spl4_9 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.18/0.48  fof(f147,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (~spl4_4 | ~spl4_9)),
% 0.18/0.48    inference(trivial_inequality_removal,[],[f146])).
% 0.18/0.48  fof(f146,plain,(
% 0.18/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (~spl4_4 | ~spl4_9)),
% 0.18/0.48    inference(forward_demodulation,[],[f144,f55])).
% 0.18/0.48  fof(f55,plain,(
% 0.18/0.48    k1_xboole_0 = sK1 | ~spl4_4),
% 0.18/0.48    inference(avatar_component_clause,[],[f53])).
% 0.18/0.48  fof(f144,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | k1_xboole_0 != sK1 | ~spl4_9),
% 0.18/0.48    inference(forward_demodulation,[],[f143,f37])).
% 0.18/0.48  fof(f37,plain,(
% 0.18/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.18/0.48    inference(equality_resolution,[],[f24])).
% 0.18/0.48  fof(f24,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f3])).
% 0.18/0.48  fof(f3,axiom,(
% 0.18/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.18/0.48  fof(f143,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | k1_xboole_0 != sK1 | ~spl4_9),
% 0.18/0.48    inference(forward_demodulation,[],[f33,f126])).
% 0.18/0.48  fof(f126,plain,(
% 0.18/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_9),
% 0.18/0.48    inference(avatar_component_clause,[],[f124])).
% 0.18/0.48  fof(f33,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 != sK1),
% 0.18/0.48    inference(definition_unfolding,[],[f16,f30])).
% 0.18/0.48  fof(f30,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f7,axiom,(
% 0.18/0.48    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).
% 0.18/0.48  fof(f16,plain,(
% 0.18/0.48    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK1),
% 0.18/0.48    inference(cnf_transformation,[],[f10])).
% 0.18/0.48  % (16990)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.48  fof(f10,plain,(
% 0.18/0.48    ? [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <~> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.18/0.48    inference(ennf_transformation,[],[f9])).
% 0.18/0.48  fof(f9,negated_conjecture,(
% 0.18/0.48    ~! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.18/0.48    inference(negated_conjecture,[],[f8])).
% 0.18/0.48  fof(f8,conjecture,(
% 0.18/0.48    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.18/0.48  fof(f138,plain,(
% 0.18/0.48    spl4_4 | spl4_5 | ~spl4_9),
% 0.18/0.48    inference(avatar_contradiction_clause,[],[f129])).
% 0.18/0.48  fof(f129,plain,(
% 0.18/0.48    $false | (spl4_4 | spl4_5 | ~spl4_9)),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f58,f54,f126,f23])).
% 0.18/0.48  fof(f23,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.18/0.48    inference(cnf_transformation,[],[f3])).
% 0.18/0.48  fof(f54,plain,(
% 0.18/0.48    k1_xboole_0 != sK1 | spl4_4),
% 0.18/0.48    inference(avatar_component_clause,[],[f53])).
% 0.18/0.48  fof(f58,plain,(
% 0.18/0.48    k1_xboole_0 != sK0 | spl4_5),
% 0.18/0.48    inference(avatar_component_clause,[],[f57])).
% 0.18/0.48  fof(f57,plain,(
% 0.18/0.48    spl4_5 <=> k1_xboole_0 = sK0),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.18/0.48  fof(f127,plain,(
% 0.18/0.48    spl4_9 | spl4_3 | ~spl4_8),
% 0.18/0.48    inference(avatar_split_clause,[],[f118,f105,f48,f124])).
% 0.18/0.48  fof(f48,plain,(
% 0.18/0.48    spl4_3 <=> k1_xboole_0 = sK2),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.18/0.48  fof(f105,plain,(
% 0.18/0.48    spl4_8 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.18/0.48  fof(f118,plain,(
% 0.18/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_8),
% 0.18/0.48    inference(trivial_inequality_removal,[],[f111])).
% 0.18/0.48  fof(f111,plain,(
% 0.18/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_8),
% 0.18/0.48    inference(superposition,[],[f23,f107])).
% 0.18/0.48  fof(f107,plain,(
% 0.18/0.48    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl4_8),
% 0.18/0.48    inference(avatar_component_clause,[],[f105])).
% 0.18/0.48  fof(f109,plain,(
% 0.18/0.48    ~spl4_5 | ~spl4_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f34,f43,f57])).
% 0.18/0.48  fof(f43,plain,(
% 0.18/0.48    spl4_2 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.18/0.48  fof(f34,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 != sK0),
% 0.18/0.48    inference(definition_unfolding,[],[f15,f30])).
% 0.18/0.48  fof(f15,plain,(
% 0.18/0.48    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK0),
% 0.18/0.48    inference(cnf_transformation,[],[f10])).
% 0.18/0.48  fof(f108,plain,(
% 0.18/0.48    spl4_8 | spl4_1 | ~spl4_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f99,f43,f39,f105])).
% 0.18/0.48  fof(f39,plain,(
% 0.18/0.48    spl4_1 <=> k1_xboole_0 = sK3),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.18/0.48  fof(f99,plain,(
% 0.18/0.48    k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl4_2),
% 0.18/0.48    inference(trivial_inequality_removal,[],[f92])).
% 0.18/0.48  fof(f92,plain,(
% 0.18/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl4_2),
% 0.18/0.48    inference(superposition,[],[f23,f44])).
% 0.18/0.48  fof(f44,plain,(
% 0.18/0.48    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl4_2),
% 0.18/0.48    inference(avatar_component_clause,[],[f43])).
% 0.18/0.48  fof(f91,plain,(
% 0.18/0.48    ~spl4_6 | spl4_2 | ~spl4_5),
% 0.18/0.48    inference(avatar_split_clause,[],[f90,f57,f43,f64])).
% 0.18/0.48  fof(f90,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (spl4_2 | ~spl4_5)),
% 0.18/0.48    inference(forward_demodulation,[],[f89,f37])).
% 0.18/0.48  fof(f89,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | (spl4_2 | ~spl4_5)),
% 0.18/0.48    inference(forward_demodulation,[],[f88,f37])).
% 0.18/0.48  fof(f88,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2),sK3) | (spl4_2 | ~spl4_5)),
% 0.18/0.48    inference(forward_demodulation,[],[f45,f59])).
% 0.18/0.48  fof(f59,plain,(
% 0.18/0.48    k1_xboole_0 = sK0 | ~spl4_5),
% 0.18/0.48    inference(avatar_component_clause,[],[f57])).
% 0.18/0.48  fof(f45,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | spl4_2),
% 0.18/0.48    inference(avatar_component_clause,[],[f43])).
% 0.18/0.48  fof(f87,plain,(
% 0.18/0.48    ~spl4_6 | spl4_2 | ~spl4_4),
% 0.18/0.48    inference(avatar_split_clause,[],[f86,f53,f43,f64])).
% 0.18/0.48  fof(f86,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (spl4_2 | ~spl4_4)),
% 0.18/0.48    inference(forward_demodulation,[],[f85,f37])).
% 0.18/0.48  fof(f85,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | (spl4_2 | ~spl4_4)),
% 0.18/0.48    inference(forward_demodulation,[],[f84,f36])).
% 0.18/0.48  fof(f36,plain,(
% 0.18/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.18/0.48    inference(equality_resolution,[],[f25])).
% 0.18/0.48  fof(f25,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f3])).
% 0.18/0.48  fof(f84,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2),sK3) | (spl4_2 | ~spl4_4)),
% 0.18/0.48    inference(forward_demodulation,[],[f45,f55])).
% 0.18/0.48  fof(f83,plain,(
% 0.18/0.48    spl4_7),
% 0.18/0.48    inference(avatar_contradiction_clause,[],[f79])).
% 0.18/0.48  fof(f79,plain,(
% 0.18/0.48    $false | spl4_7),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f36,f77])).
% 0.18/0.48  fof(f77,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0) | spl4_7),
% 0.18/0.48    inference(avatar_component_clause,[],[f75])).
% 0.18/0.48  fof(f75,plain,(
% 0.18/0.48    spl4_7 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.18/0.48  fof(f78,plain,(
% 0.18/0.48    ~spl4_7 | ~spl4_1 | spl4_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f73,f43,f39,f75])).
% 0.18/0.48  fof(f73,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0) | (~spl4_1 | spl4_2)),
% 0.18/0.48    inference(forward_demodulation,[],[f45,f40])).
% 0.18/0.48  fof(f40,plain,(
% 0.18/0.48    k1_xboole_0 = sK3 | ~spl4_1),
% 0.18/0.48    inference(avatar_component_clause,[],[f39])).
% 0.18/0.48  fof(f72,plain,(
% 0.18/0.48    spl4_6),
% 0.18/0.48    inference(avatar_contradiction_clause,[],[f68])).
% 0.18/0.48  fof(f68,plain,(
% 0.18/0.48    $false | spl4_6),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f37,f66])).
% 0.18/0.48  fof(f66,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | spl4_6),
% 0.18/0.48    inference(avatar_component_clause,[],[f64])).
% 0.18/0.48  fof(f67,plain,(
% 0.18/0.48    ~spl4_6 | spl4_2 | ~spl4_3),
% 0.18/0.48    inference(avatar_split_clause,[],[f62,f48,f43,f64])).
% 0.18/0.48  fof(f62,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (spl4_2 | ~spl4_3)),
% 0.18/0.48    inference(forward_demodulation,[],[f61,f36])).
% 0.18/0.48  fof(f61,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0),sK3) | (spl4_2 | ~spl4_3)),
% 0.18/0.48    inference(backward_demodulation,[],[f45,f49])).
% 0.18/0.48  fof(f49,plain,(
% 0.18/0.48    k1_xboole_0 = sK2 | ~spl4_3),
% 0.18/0.48    inference(avatar_component_clause,[],[f48])).
% 0.18/0.48  fof(f60,plain,(
% 0.18/0.48    spl4_1 | spl4_3 | spl4_4 | spl4_5 | spl4_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f35,f43,f57,f53,f48,f39])).
% 0.18/0.48  fof(f35,plain,(
% 0.18/0.48    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3),
% 0.18/0.48    inference(definition_unfolding,[],[f14,f30])).
% 0.18/0.48  fof(f14,plain,(
% 0.18/0.48    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3),
% 0.18/0.48    inference(cnf_transformation,[],[f10])).
% 0.18/0.48  fof(f51,plain,(
% 0.18/0.48    ~spl4_3 | ~spl4_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f32,f43,f48])).
% 0.18/0.48  fof(f32,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 != sK2),
% 0.18/0.48    inference(definition_unfolding,[],[f17,f30])).
% 0.18/0.48  fof(f17,plain,(
% 0.18/0.48    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK2),
% 0.18/0.48    inference(cnf_transformation,[],[f10])).
% 0.18/0.48  fof(f46,plain,(
% 0.18/0.48    ~spl4_1 | ~spl4_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f31,f43,f39])).
% 0.18/0.48  fof(f31,plain,(
% 0.18/0.48    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 != sK3),
% 0.18/0.48    inference(definition_unfolding,[],[f18,f30])).
% 0.18/0.48  fof(f18,plain,(
% 0.18/0.48    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 != sK3),
% 0.18/0.48    inference(cnf_transformation,[],[f10])).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (17001)------------------------------
% 0.18/0.48  % (17001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (17001)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (17001)Memory used [KB]: 10746
% 0.18/0.48  % (17001)Time elapsed: 0.031 s
% 0.18/0.48  % (17001)------------------------------
% 0.18/0.48  % (17001)------------------------------
% 0.18/0.48  % (16975)Success in time 0.137 s
%------------------------------------------------------------------------------
