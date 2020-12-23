%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 122 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  186 ( 304 expanded)
%              Number of equality atoms :   74 ( 137 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f49,f66,f85,f89,f104,f109,f114,f128,f138,f151])).

fof(f151,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl3_1
    | spl3_2
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f149,f40])).

fof(f40,plain,
    ( k1_xboole_0 != sK0
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f149,plain,
    ( k1_xboole_0 = sK0
    | spl3_2
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f147,f44])).

fof(f44,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f147,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_16 ),
    inference(trivial_inequality_removal,[],[f146])).

fof(f146,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_16 ),
    inference(superposition,[],[f29,f137])).

fof(f137,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_16
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f138,plain,
    ( spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f129,f53,f136])).

fof(f53,plain,
    ( spl3_4
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f129,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f127,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f127,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f128,plain,
    ( spl3_4
    | spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f51,f47,f68,f53])).

fof(f68,plain,
    ( spl3_8
  <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f47,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f51,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f48,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f48,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f114,plain,
    ( ~ spl3_7
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f110,f65])).

fof(f65,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_7
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f110,plain,
    ( sK2 != k1_mcart_1(sK2)
    | ~ spl3_12 ),
    inference(superposition,[],[f35,f92])).

fof(f92,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_12
  <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f35,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k1_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f109,plain,
    ( spl3_12
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f93,f87,f64,f91])).

fof(f87,plain,
    ( spl3_11
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f93,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f88,f65])).

fof(f88,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f104,plain,(
    ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f96,f97])).

fof(f97,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl3_10 ),
    inference(superposition,[],[f22,f84])).

fof(f84,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_10
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f22,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f96,plain,
    ( sK2 != k2_mcart_1(sK2)
    | ~ spl3_10 ),
    inference(superposition,[],[f34,f84])).

fof(f34,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k2_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

% (24411)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f89,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f80,f68,f87])).

fof(f80,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f79,f32])).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f79,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_8 ),
    inference(resolution,[],[f69,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f69,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f85,plain,
    ( spl3_10
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f81,f68,f61,f83])).

fof(f61,plain,
    ( spl3_6
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f81,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f80,f62])).

fof(f62,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f66,plain,
    ( spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f16,f64,f61])).

fof(f16,plain,
    ( sK2 = k1_mcart_1(sK2)
    | sK2 = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

% (24418)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => ( k2_mcart_1(X2) != X2
                  & k1_mcart_1(X2) != X2 ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f47])).

fof(f17,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:04:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (24407)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (24407)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f41,f45,f49,f66,f85,f89,f104,f109,f114,f128,f138,f151])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    spl3_1 | spl3_2 | ~spl3_16),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f150])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    $false | (spl3_1 | spl3_2 | ~spl3_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f149,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl3_1 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | (spl3_2 | ~spl3_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f147,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl3_2 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl3_16),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f146])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl3_16),
% 0.21/0.48    inference(superposition,[],[f29,f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f136])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl3_16 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    spl3_16 | ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f129,f53,f136])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl3_4 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_4),
% 0.21/0.48    inference(resolution,[],[f127,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f53])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl3_4 | spl3_8 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f51,f47,f68,f53])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl3_8 <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl3_3 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.48    inference(resolution,[],[f48,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f47])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ~spl3_7 | ~spl3_12),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f113])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    $false | (~spl3_7 | ~spl3_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f110,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    sK2 = k1_mcart_1(sK2) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl3_7 <=> sK2 = k1_mcart_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    sK2 != k1_mcart_1(sK2) | ~spl3_12),
% 0.21/0.48    inference(superposition,[],[f35,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl3_12 <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k1_mcart_1(X0) != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl3_12 | ~spl3_7 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f93,f87,f64,f91])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl3_11 <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | (~spl3_7 | ~spl3_11)),
% 0.21/0.48    inference(forward_demodulation,[],[f88,f65])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ~spl3_10),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    $false | ~spl3_10),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    sK2 = k2_mcart_1(sK2) | ~spl3_10),
% 0.21/0.48    inference(superposition,[],[f22,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl3_10 <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    sK2 != k2_mcart_1(sK2) | ~spl3_10),
% 0.21/0.48    inference(superposition,[],[f34,f84])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k2_mcart_1(X0) != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  % (24411)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl3_11 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f80,f68,f87])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_8),
% 0.21/0.48    inference(subsumption_resolution,[],[f79,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_8),
% 0.21/0.48    inference(resolution,[],[f69,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl3_10 | ~spl3_6 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f81,f68,f61,f83])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl3_6 <=> sK2 = k2_mcart_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | (~spl3_6 | ~spl3_8)),
% 0.21/0.48    inference(forward_demodulation,[],[f80,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    sK2 = k2_mcart_1(sK2) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl3_6 | spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f64,f61])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    sK2 = k1_mcart_1(sK2) | sK2 = k2_mcart_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  % (24418)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f47])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f43])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f39])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (24407)------------------------------
% 0.21/0.48  % (24407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24407)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (24407)Memory used [KB]: 6140
% 0.21/0.48  % (24407)Time elapsed: 0.066 s
% 0.21/0.48  % (24407)------------------------------
% 0.21/0.48  % (24407)------------------------------
% 0.21/0.49  % (24406)Success in time 0.126 s
%------------------------------------------------------------------------------
