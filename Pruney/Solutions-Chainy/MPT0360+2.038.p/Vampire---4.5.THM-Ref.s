%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 126 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  196 ( 328 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f108,f111,f118,f130,f137,f148,f161,f170,f181])).

fof(f181,plain,
    ( ~ spl4_16
    | spl4_1
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f176,f167,f42,f145])).

fof(f145,plain,
    ( spl4_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f42,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f167,plain,
    ( spl4_18
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f176,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_18 ),
    inference(resolution,[],[f169,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f29,f23])).

fof(f23,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f169,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f167])).

fof(f170,plain,
    ( spl4_18
    | ~ spl4_3
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f162,f158,f52,f167])).

fof(f52,plain,
    ( spl4_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f158,plain,
    ( spl4_17
  <=> r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f162,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_17 ),
    inference(resolution,[],[f160,f119])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f35,f54])).

fof(f54,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f160,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f158])).

fof(f161,plain,
    ( spl4_17
    | ~ spl4_16
    | ~ spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f155,f47,f57,f145,f158])).

fof(f57,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f47,plain,
    ( spl4_2
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f155,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f30,f49])).

fof(f49,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X2,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f148,plain,
    ( spl4_16
    | spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f143,f134,f101,f145])).

fof(f101,plain,
    ( spl4_11
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f134,plain,
    ( spl4_15
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f143,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_15 ),
    inference(resolution,[],[f136,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f136,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f137,plain,
    ( spl4_15
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f132,f127,f134])).

fof(f127,plain,
    ( spl4_14
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f132,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_14 ),
    inference(resolution,[],[f129,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f129,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f130,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f125,f115,f52,f127])).

fof(f115,plain,
    ( spl4_13
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f125,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(resolution,[],[f119,f117])).

fof(f117,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f118,plain,
    ( spl4_13
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f112,f105,f115])).

fof(f105,plain,
    ( spl4_12
  <=> r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f112,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_12 ),
    inference(resolution,[],[f107,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f107,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f111,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl4_11 ),
    inference(resolution,[],[f103,f22])).

fof(f22,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f103,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f108,plain,
    ( spl4_11
    | spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f99,f57,f105,f101])).

fof(f99,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f27,f59])).

fof(f59,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f18,f57])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f55,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f52])).

fof(f19,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:00:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (2667)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (2659)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (2675)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (2659)Refutation not found, incomplete strategy% (2659)------------------------------
% 0.22/0.52  % (2659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2667)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (2659)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2659)Memory used [KB]: 10746
% 0.22/0.52  % (2659)Time elapsed: 0.113 s
% 0.22/0.52  % (2659)------------------------------
% 0.22/0.52  % (2659)------------------------------
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f108,f111,f118,f130,f137,f148,f161,f170,f181])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ~spl4_16 | spl4_1 | ~spl4_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f176,f167,f42,f145])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    spl4_16 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    spl4_1 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    spl4_18 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_18),
% 0.22/0.53    inference(resolution,[],[f169,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f29,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl4_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f167])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    spl4_18 | ~spl4_3 | ~spl4_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f162,f158,f52,f167])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    spl4_3 <=> r1_tarski(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    spl4_17 <=> r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | (~spl4_3 | ~spl4_17)),
% 0.22/0.53    inference(resolution,[],[f160,f119])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK2,X0) | r1_tarski(sK1,X0)) ) | ~spl4_3),
% 0.22/0.53    inference(resolution,[],[f35,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f52])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~spl4_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f158])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    spl4_17 | ~spl4_16 | ~spl4_4 | ~spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f155,f47,f57,f145,f158])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl4_2 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~spl4_2),
% 0.22/0.53    inference(resolution,[],[f30,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f47])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X2,k3_subset_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    spl4_16 | spl4_11 | ~spl4_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f143,f134,f101,f145])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl4_11 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    spl4_15 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    v1_xboole_0(k1_zfmisc_1(sK0)) | m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_15),
% 0.22/0.53    inference(resolution,[],[f136,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f134])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    spl4_15 | ~spl4_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f132,f127,f134])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    spl4_14 <=> r1_tarski(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_14),
% 0.22/0.53    inference(resolution,[],[f129,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    r1_tarski(sK1,sK0) | ~spl4_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f127])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    spl4_14 | ~spl4_3 | ~spl4_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f125,f115,f52,f127])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    spl4_13 <=> r1_tarski(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    r1_tarski(sK1,sK0) | (~spl4_3 | ~spl4_13)),
% 0.22/0.53    inference(resolution,[],[f119,f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    r1_tarski(sK2,sK0) | ~spl4_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f115])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    spl4_13 | ~spl4_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f112,f105,f115])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl4_12 <=> r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    r1_tarski(sK2,sK0) | ~spl4_12),
% 0.22/0.53    inference(resolution,[],[f107,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl4_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f105])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ~spl4_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f109])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    $false | ~spl4_11),
% 0.22/0.53    inference(resolution,[],[f103,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f101])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl4_11 | spl4_12 | ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f99,f57,f105,f101])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.22/0.53    inference(resolution,[],[f27,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f57])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f18,f57])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f19,f52])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f20,f47])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ~spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f21,f42])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    k1_xboole_0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (2667)------------------------------
% 0.22/0.53  % (2667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2667)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (2667)Memory used [KB]: 10746
% 0.22/0.53  % (2667)Time elapsed: 0.122 s
% 0.22/0.53  % (2667)------------------------------
% 0.22/0.53  % (2667)------------------------------
% 0.22/0.53  % (2650)Success in time 0.164 s
%------------------------------------------------------------------------------
