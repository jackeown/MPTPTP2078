%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 165 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  246 ( 407 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f740,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f109,f153,f167,f185,f244,f277,f283,f585,f596,f739])).

fof(f739,plain,
    ( spl5_1
    | ~ spl5_53 ),
    inference(avatar_split_clause,[],[f738,f582,f56])).

fof(f56,plain,
    ( spl5_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f582,plain,
    ( spl5_53
  <=> v1_xboole_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f738,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_53 ),
    inference(resolution,[],[f610,f39])).

fof(f39,plain,(
    ! [X0] : ~ v1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f610,plain,
    ( ! [X1] :
        ( v1_subset_1(sK3(sK0),X1)
        | v1_xboole_0(X1) )
    | ~ spl5_53 ),
    inference(resolution,[],[f584,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f48,f80,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f46,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f584,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f582])).

fof(f596,plain,
    ( ~ spl5_15
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f587,f578,f182])).

fof(f182,plain,
    ( spl5_15
  <=> v1_subset_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f578,plain,
    ( spl5_52
  <=> sK0 = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f587,plain,
    ( ~ v1_subset_1(sK0,sK0)
    | ~ spl5_52 ),
    inference(superposition,[],[f39,f580])).

fof(f580,plain,
    ( sK0 = sK3(sK0)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f578])).

fof(f585,plain,
    ( spl5_52
    | spl5_53
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f576,f61,f582,f578])).

fof(f61,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f576,plain,
    ( v1_xboole_0(sK3(sK0))
    | sK0 = sK3(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f572,f63])).

fof(f63,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f572,plain,(
    ! [X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(sK3(X1))
      | sK3(X1) = X1 ) ),
    inference(global_subsumption,[],[f464,f129])).

fof(f129,plain,(
    ! [X1] :
      ( v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(sK3(X1))
      | sK3(X1) = X1 ) ),
    inference(resolution,[],[f35,f77])).

fof(f77,plain,(
    ! [X0] : r1_tarski(sK3(X0),X0) ),
    inference(resolution,[],[f49,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

% (19643)Refutation not found, incomplete strategy% (19643)------------------------------
% (19643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19643)Termination reason: Refutation not found, incomplete strategy

% (19643)Memory used [KB]: 10618
% (19643)Time elapsed: 0.108 s
% (19643)------------------------------
% (19643)------------------------------
fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f464,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(X2)
      | v1_xboole_0(sK3(X2)) ) ),
    inference(resolution,[],[f303,f37])).

fof(f303,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK3(X1)),X1)
      | v1_xboole_0(sK3(X1)) ) ),
    inference(resolution,[],[f85,f77])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(sK2(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f283,plain,(
    ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl5_26 ),
    inference(resolution,[],[f276,f51])).

fof(f51,plain,(
    ! [X0] : ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f276,plain,
    ( v1_xboole_0(k2_tarski(sK1,sK1))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl5_26
  <=> v1_xboole_0(k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f277,plain,
    ( spl5_26
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f257,f164,f150,f274])).

fof(f150,plain,
    ( spl5_10
  <=> k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f164,plain,
    ( spl5_12
  <=> v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f257,plain,
    ( v1_xboole_0(k2_tarski(sK1,sK1))
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f166,f152])).

fof(f152,plain,
    ( k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f166,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f244,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f241,f106,f113])).

fof(f113,plain,
    ( spl5_6
  <=> r1_tarski(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f106,plain,
    ( spl5_5
  <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f241,plain,
    ( r1_tarski(k6_domain_1(sK0,sK1),sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f108,f49])).

fof(f108,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f185,plain,
    ( spl5_15
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f180,f160,f66,f182])).

fof(f66,plain,
    ( spl5_3
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f160,plain,
    ( spl5_11
  <=> sK0 = k6_domain_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f180,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f68,f162])).

fof(f162,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f160])).

fof(f68,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f167,plain,
    ( spl5_11
    | spl5_12
    | ~ spl5_2
    | spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f154,f113,f56,f61,f164,f160])).

fof(f154,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(k6_domain_1(sK0,sK1))
    | sK0 = k6_domain_1(sK0,sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f115,f35])).

fof(f115,plain,
    ( r1_tarski(k6_domain_1(sK0,sK1),sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f153,plain,
    ( spl5_10
    | spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f146,f71,f56,f150])).

fof(f71,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f146,plain,
    ( v1_xboole_0(sK0)
    | k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f52,f73])).

fof(f73,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f40,f33])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f109,plain,
    ( spl5_5
    | spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f101,f71,f56,f106])).

fof(f101,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f41,f73])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f74,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f69,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:47:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (19626)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.49  % (19637)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.49  % (19628)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (19628)Refutation not found, incomplete strategy% (19628)------------------------------
% 0.21/0.49  % (19628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19637)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (19628)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19628)Memory used [KB]: 10746
% 0.21/0.50  % (19628)Time elapsed: 0.076 s
% 0.21/0.50  % (19628)------------------------------
% 0.21/0.50  % (19628)------------------------------
% 0.21/0.50  % (19643)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f740,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f109,f153,f167,f185,f244,f277,f283,f585,f596,f739])).
% 0.21/0.50  fof(f739,plain,(
% 0.21/0.50    spl5_1 | ~spl5_53),
% 0.21/0.50    inference(avatar_split_clause,[],[f738,f582,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl5_1 <=> v1_xboole_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f582,plain,(
% 0.21/0.50    spl5_53 <=> v1_xboole_0(sK3(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 0.21/0.50  fof(f738,plain,(
% 0.21/0.50    v1_xboole_0(sK0) | ~spl5_53),
% 0.21/0.50    inference(resolution,[],[f610,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_subset_1(sK3(X0),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.21/0.50  fof(f610,plain,(
% 0.21/0.50    ( ! [X1] : (v1_subset_1(sK3(sK0),X1) | v1_xboole_0(X1)) ) | ~spl5_53),
% 0.21/0.50    inference(resolution,[],[f584,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(global_subsumption,[],[f48,f80,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_subset_1(X1,X0) | ~v1_xboole_0(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f46,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f584,plain,(
% 0.21/0.50    v1_xboole_0(sK3(sK0)) | ~spl5_53),
% 0.21/0.50    inference(avatar_component_clause,[],[f582])).
% 0.21/0.50  fof(f596,plain,(
% 0.21/0.50    ~spl5_15 | ~spl5_52),
% 0.21/0.50    inference(avatar_split_clause,[],[f587,f578,f182])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    spl5_15 <=> v1_subset_1(sK0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.50  fof(f578,plain,(
% 0.21/0.50    spl5_52 <=> sK0 = sK3(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.21/0.50  fof(f587,plain,(
% 0.21/0.50    ~v1_subset_1(sK0,sK0) | ~spl5_52),
% 0.21/0.50    inference(superposition,[],[f39,f580])).
% 0.21/0.50  fof(f580,plain,(
% 0.21/0.50    sK0 = sK3(sK0) | ~spl5_52),
% 0.21/0.50    inference(avatar_component_clause,[],[f578])).
% 0.21/0.50  fof(f585,plain,(
% 0.21/0.50    spl5_52 | spl5_53 | ~spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f576,f61,f582,f578])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    spl5_2 <=> v1_zfmisc_1(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f576,plain,(
% 0.21/0.50    v1_xboole_0(sK3(sK0)) | sK0 = sK3(sK0) | ~spl5_2),
% 0.21/0.50    inference(resolution,[],[f572,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    v1_zfmisc_1(sK0) | ~spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f61])).
% 0.21/0.50  fof(f572,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(sK3(X1)) | sK3(X1) = X1) )),
% 0.21/0.50    inference(global_subsumption,[],[f464,f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X1] : (v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(sK3(X1)) | sK3(X1) = X1) )),
% 0.21/0.50    inference(resolution,[],[f35,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(sK3(X0),X0)) )),
% 0.21/0.50    inference(resolution,[],[f49,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  % (19643)Refutation not found, incomplete strategy% (19643)------------------------------
% 0.21/0.50  % (19643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19643)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19643)Memory used [KB]: 10618
% 0.21/0.50  % (19643)Time elapsed: 0.108 s
% 0.21/0.50  % (19643)------------------------------
% 0.21/0.50  % (19643)------------------------------
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X0) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.50  fof(f464,plain,(
% 0.21/0.50    ( ! [X2] : (~v1_xboole_0(X2) | v1_xboole_0(sK3(X2))) )),
% 0.21/0.50    inference(resolution,[],[f303,f37])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(sK2(sK3(X1)),X1) | v1_xboole_0(sK3(X1))) )),
% 0.21/0.50    inference(resolution,[],[f85,f77])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(sK2(X0),X1) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(resolution,[],[f45,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    ~spl5_26),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f280])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    $false | ~spl5_26),
% 0.21/0.50    inference(resolution,[],[f276,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k2_tarski(X0,X0))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f32,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    v1_xboole_0(k2_tarski(sK1,sK1)) | ~spl5_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f274])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    spl5_26 <=> v1_xboole_0(k2_tarski(sK1,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    spl5_26 | ~spl5_10 | ~spl5_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f257,f164,f150,f274])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl5_10 <=> k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    spl5_12 <=> v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    v1_xboole_0(k2_tarski(sK1,sK1)) | (~spl5_10 | ~spl5_12)),
% 0.21/0.50    inference(backward_demodulation,[],[f166,f152])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) | ~spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f150])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~spl5_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f164])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    spl5_6 | ~spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f241,f106,f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl5_6 <=> r1_tarski(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl5_5 <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    r1_tarski(k6_domain_1(sK0,sK1),sK0) | ~spl5_5),
% 0.21/0.50    inference(resolution,[],[f108,f49])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    spl5_15 | ~spl5_3 | ~spl5_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f180,f160,f66,f182])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl5_3 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    spl5_11 <=> sK0 = k6_domain_1(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    v1_subset_1(sK0,sK0) | (~spl5_3 | ~spl5_11)),
% 0.21/0.50    inference(backward_demodulation,[],[f68,f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    sK0 = k6_domain_1(sK0,sK1) | ~spl5_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f160])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    spl5_11 | spl5_12 | ~spl5_2 | spl5_1 | ~spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f154,f113,f56,f61,f164,f160])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    v1_xboole_0(sK0) | ~v1_zfmisc_1(sK0) | v1_xboole_0(k6_domain_1(sK0,sK1)) | sK0 = k6_domain_1(sK0,sK1) | ~spl5_6),
% 0.21/0.50    inference(resolution,[],[f115,f35])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    r1_tarski(k6_domain_1(sK0,sK1),sK0) | ~spl5_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f113])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    spl5_10 | spl5_1 | ~spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f146,f71,f56,f150])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    spl5_4 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    v1_xboole_0(sK0) | k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f52,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    m1_subset_1(sK1,sK0) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f71])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f40,f33])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl5_5 | spl5_1 | ~spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f101,f71,f56,f106])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    v1_xboole_0(sK0) | m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f41,f73])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f71])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    m1_subset_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f66])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f61])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    v1_zfmisc_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ~spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f56])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ~v1_xboole_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (19637)------------------------------
% 0.21/0.50  % (19637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19637)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (19637)Memory used [KB]: 11129
% 0.21/0.50  % (19637)Time elapsed: 0.091 s
% 0.21/0.50  % (19637)------------------------------
% 0.21/0.50  % (19637)------------------------------
% 0.21/0.51  % (19617)Success in time 0.146 s
%------------------------------------------------------------------------------
