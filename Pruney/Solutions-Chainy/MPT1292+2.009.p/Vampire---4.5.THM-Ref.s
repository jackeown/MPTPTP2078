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
% DateTime   : Thu Dec  3 13:13:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 123 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :  189 ( 321 expanded)
%              Number of equality atoms :   45 (  87 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f77,f85,f108,f129,f156,f164,f177,f178])).

fof(f178,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f177,plain,
    ( spl4_9
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f171,f101,f105])).

fof(f105,plain,
    ( spl4_9
  <=> k1_xboole_0 = k3_tarski(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f101,plain,
    ( spl4_8
  <=> k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f171,plain,
    ( k1_xboole_0 = k3_tarski(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_8 ),
    inference(trivial_inequality_removal,[],[f170])).

fof(f170,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_tarski(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_8 ),
    inference(superposition,[],[f29,f103])).

fof(f103,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK2(X0)
      | k1_xboole_0 = k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

fof(f164,plain,
    ( spl4_14
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f157,f153,f161])).

fof(f161,plain,
    ( spl4_14
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f153,plain,
    ( spl4_13
  <=> r1_tarski(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f157,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl4_13 ),
    inference(resolution,[],[f155,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f155,plain,
    ( r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f153])).

fof(f156,plain,
    ( spl4_13
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f151,f126,f74,f153])).

fof(f74,plain,
    ( spl4_6
  <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f126,plain,
    ( spl4_10
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f151,plain,
    ( r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(resolution,[],[f143,f76])).

fof(f76,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f143,plain,
    ( ! [X3] :
        ( ~ m1_setfam_1(k1_xboole_0,X3)
        | r1_tarski(X3,k1_xboole_0) )
    | ~ spl4_10 ),
    inference(superposition,[],[f38,f128])).

fof(f128,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f129,plain,
    ( spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f122,f105,f126])).

fof(f122,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl4_9 ),
    inference(resolution,[],[f118,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k3_tarski(X0) )
    | ~ spl4_9 ),
    inference(resolution,[],[f110,f32])).

fof(f110,plain,
    ( ! [X1] :
        ( r1_tarski(k3_tarski(X1),k1_xboole_0)
        | ~ r1_tarski(X1,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_9 ),
    inference(superposition,[],[f34,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k3_tarski(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f108,plain,
    ( spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f97,f105,f101])).

fof(f97,plain,
    ( k1_xboole_0 = k3_tarski(k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f87,f32])).

fof(f87,plain,(
    ! [X0] :
      ( r1_tarski(sK2(k1_zfmisc_1(X0)),X0)
      | k1_xboole_0 = k3_tarski(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f30,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,
    ( ~ spl4_7
    | spl4_2
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f80,f48,f53,f82])).

fof(f82,plain,
    ( spl4_7
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f53,plain,
    ( spl4_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f48,plain,
    ( spl4_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f80,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f33,f50])).

fof(f50,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f77,plain,
    ( spl4_6
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f72,f63,f58,f74])).

fof(f58,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f63,plain,
    ( spl4_4
  <=> m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f72,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f65,f60])).

fof(f60,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f65,plain,
    ( m1_setfam_1(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f71,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f68])).

fof(f68,plain,
    ( spl4_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f66,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f23,f63])).

fof(f23,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

fof(f61,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:47:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (17598)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.47  % (17605)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (17597)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.48  % (17606)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.48  % (17597)Refutation not found, incomplete strategy% (17597)------------------------------
% 0.21/0.48  % (17597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17597)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (17597)Memory used [KB]: 10618
% 0.21/0.48  % (17597)Time elapsed: 0.005 s
% 0.21/0.48  % (17597)------------------------------
% 0.21/0.48  % (17597)------------------------------
% 0.21/0.48  % (17606)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f77,f85,f108,f129,f156,f164,f177,f178])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    k1_xboole_0 != u1_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    spl4_9 | ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f171,f101,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl4_9 <=> k1_xboole_0 = k3_tarski(k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl4_8 <=> k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    k1_xboole_0 = k3_tarski(k1_zfmisc_1(k1_xboole_0)) | ~spl4_8),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f170])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_tarski(k1_zfmisc_1(k1_xboole_0)) | ~spl4_8),
% 0.21/0.48    inference(superposition,[],[f29,f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) | ~spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != sK2(X0) | k1_xboole_0 = k3_tarski(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.21/0.48    inference(rectify,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    spl4_14 | ~spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f157,f153,f161])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl4_14 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    spl4_13 <=> r1_tarski(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    k1_xboole_0 = u1_struct_0(sK0) | ~spl4_13),
% 0.21/0.48    inference(resolution,[],[f155,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    r1_tarski(u1_struct_0(sK0),k1_xboole_0) | ~spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f153])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl4_13 | ~spl4_6 | ~spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f151,f126,f74,f153])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl4_6 <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl4_10 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    r1_tarski(u1_struct_0(sK0),k1_xboole_0) | (~spl4_6 | ~spl4_10)),
% 0.21/0.48    inference(resolution,[],[f143,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ( ! [X3] : (~m1_setfam_1(k1_xboole_0,X3) | r1_tarski(X3,k1_xboole_0)) ) | ~spl4_10),
% 0.21/0.48    inference(superposition,[],[f38,f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl4_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f126])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_setfam_1(X1,X0) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl4_10 | ~spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f122,f105,f126])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl4_9),
% 0.21/0.48    inference(resolution,[],[f118,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k3_tarski(X0)) ) | ~spl4_9),
% 0.21/0.48    inference(resolution,[],[f110,f32])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(k3_tarski(X1),k1_xboole_0) | ~r1_tarski(X1,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_9),
% 0.21/0.48    inference(superposition,[],[f34,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    k1_xboole_0 = k3_tarski(k1_zfmisc_1(k1_xboole_0)) | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f105])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl4_8 | spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f97,f105,f101])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    k1_xboole_0 = k3_tarski(k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    inference(resolution,[],[f87,f32])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(sK2(k1_zfmisc_1(X0)),X0) | k1_xboole_0 = k3_tarski(k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(resolution,[],[f30,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = k3_tarski(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~spl4_7 | spl4_2 | ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f80,f48,f53,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl4_7 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl4_2 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl4_1 <=> l1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0)) | ~spl4_1),
% 0.21/0.48    inference(resolution,[],[f33,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    l1_struct_0(sK0) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f48])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl4_6 | ~spl4_3 | ~spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f72,f63,f58,f74])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl4_3 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl4_4 <=> m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | (~spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(backward_demodulation,[],[f65,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f58])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    m1_setfam_1(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl4_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f63])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f58])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    k1_xboole_0 = sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f53])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f48])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    l1_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17606)------------------------------
% 0.21/0.48  % (17606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17606)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17606)Memory used [KB]: 6140
% 0.21/0.48  % (17606)Time elapsed: 0.070 s
% 0.21/0.48  % (17606)------------------------------
% 0.21/0.48  % (17606)------------------------------
% 0.21/0.48  % (17589)Success in time 0.127 s
%------------------------------------------------------------------------------
