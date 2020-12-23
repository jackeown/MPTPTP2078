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
% DateTime   : Thu Dec  3 12:45:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 139 expanded)
%              Number of leaves         :   19 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  204 ( 334 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f72,f84,f103,f111,f116,f127,f193,f207,f210])).

fof(f210,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f71,f208])).

fof(f208,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl4_1
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f91,f199])).

fof(f199,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK2)
        | r1_xboole_0(X1,k4_xboole_0(sK0,sK2)) )
    | ~ spl4_23 ),
    inference(superposition,[],[f25,f192])).

fof(f192,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl4_23
  <=> sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f91,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f20,f49])).

fof(f49,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f42,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f20,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f71,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_5
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f207,plain,
    ( spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f205,f96])).

fof(f96,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f205,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f204,f192])).

fof(f204,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(resolution,[],[f123,f102])).

fof(f102,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_6
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK1,X0)
        | r1_tarski(sK1,k4_xboole_0(sK0,X0)) )
    | ~ spl4_11 ),
    inference(resolution,[],[f115,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f115,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f193,plain,
    ( spl4_23
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f138,f125,f41,f191])).

fof(f125,plain,
    ( spl4_13
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f138,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f133,f53])).

fof(f53,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f50,f49])).

fof(f50,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f42,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f133,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_13 ),
    inference(resolution,[],[f126,f31])).

fof(f126,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( spl4_13
    | ~ spl4_1
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f112,f109,f41,f125])).

fof(f109,plain,
    ( spl4_10
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f112,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_1
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f110,f49])).

fof(f110,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f116,plain,
    ( spl4_11
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f106,f82,f114])).

fof(f82,plain,
    ( spl4_7
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f106,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f83,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f83,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f111,plain,
    ( spl4_10
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f48,f41,f109])).

fof(f48,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f103,plain,
    ( spl4_6
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f92,f67,f41,f78])).

fof(f67,plain,
    ( spl4_4
  <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f92,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f68,f49])).

fof(f68,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f84,plain,
    ( spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f45,f82])).

fof(f45,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f61,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f59,f37])).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f59,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f46,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f46,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f72,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f19,f70,f67])).

fof(f19,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f45])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:58:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (14232)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (14232)Refutation not found, incomplete strategy% (14232)------------------------------
% 0.21/0.48  % (14232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14232)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14232)Memory used [KB]: 10490
% 0.21/0.48  % (14232)Time elapsed: 0.005 s
% 0.21/0.48  % (14232)------------------------------
% 0.21/0.48  % (14232)------------------------------
% 0.21/0.49  % (14212)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (14226)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (14212)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f43,f47,f72,f84,f103,f111,f116,f127,f193,f207,f210])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_5 | ~spl4_23),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f209])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    $false | (~spl4_1 | ~spl4_5 | ~spl4_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f71,f208])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ~r1_tarski(sK1,sK2) | (~spl4_1 | ~spl4_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f91,f199])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tarski(X1,sK2) | r1_xboole_0(X1,k4_xboole_0(sK0,sK2))) ) | ~spl4_23),
% 0.21/0.49    inference(superposition,[],[f25,f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl4_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f191])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl4_23 <=> sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~r1_tarski(sK1,sK2) | ~spl4_1),
% 0.21/0.49    inference(forward_demodulation,[],[f20,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl4_1),
% 0.21/0.49    inference(resolution,[],[f42,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl4_5 <=> r1_tarski(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    spl4_5 | ~spl4_6 | ~spl4_11 | ~spl4_23),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    $false | (spl4_5 | ~spl4_6 | ~spl4_11 | ~spl4_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f205,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ~r1_tarski(sK1,sK2) | spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f70])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2) | (~spl4_6 | ~spl4_11 | ~spl4_23)),
% 0.21/0.49    inference(forward_demodulation,[],[f204,f192])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (~spl4_6 | ~spl4_11)),
% 0.21/0.49    inference(resolution,[],[f123,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl4_6 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_xboole_0(sK1,X0) | r1_tarski(sK1,k4_xboole_0(sK0,X0))) ) | ~spl4_11),
% 0.21/0.49    inference(resolution,[],[f115,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    r1_tarski(sK1,sK0) | ~spl4_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl4_11 <=> r1_tarski(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    spl4_23 | ~spl4_1 | ~spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f138,f125,f41,f191])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl4_13 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl4_1 | ~spl4_13)),
% 0.21/0.49    inference(forward_demodulation,[],[f133,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | ~spl4_1),
% 0.21/0.49    inference(forward_demodulation,[],[f50,f49])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | ~spl4_1),
% 0.21/0.49    inference(resolution,[],[f42,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl4_13),
% 0.21/0.49    inference(resolution,[],[f126,f31])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl4_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f125])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl4_13 | ~spl4_1 | ~spl4_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f112,f109,f41,f125])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl4_10 <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl4_1 | ~spl4_10)),
% 0.21/0.49    inference(forward_demodulation,[],[f110,f49])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl4_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f109])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl4_11 | ~spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f106,f82,f114])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl4_7 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    r1_tarski(sK1,sK0) | ~spl4_7),
% 0.21/0.49    inference(resolution,[],[f83,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    spl4_10 | ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f41,f109])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl4_1),
% 0.21/0.49    inference(resolution,[],[f42,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl4_6 | ~spl4_1 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f92,f67,f41,f78])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl4_4 <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (~spl4_1 | ~spl4_4)),
% 0.21/0.49    inference(forward_demodulation,[],[f68,f49])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl4_7 | ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f61,f45,f82])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl4_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f59,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.21/0.49    inference(resolution,[],[f46,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl4_4 | spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f70,f67])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f45])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f41])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (14212)------------------------------
% 0.21/0.49  % (14212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14212)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (14212)Memory used [KB]: 6268
% 0.21/0.49  % (14212)Time elapsed: 0.063 s
% 0.21/0.49  % (14212)------------------------------
% 0.21/0.49  % (14212)------------------------------
% 0.21/0.49  % (14215)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (14211)Success in time 0.132 s
%------------------------------------------------------------------------------
