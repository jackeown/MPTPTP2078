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
% DateTime   : Thu Dec  3 13:20:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 186 expanded)
%              Number of leaves         :   26 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  324 ( 598 expanded)
%              Number of equality atoms :   33 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f72,f77,f87,f94,f111,f122,f138,f146,f151,f155,f159])).

fof(f159,plain,
    ( spl3_5
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f156,f109,f62,f70])).

fof(f70,plain,
    ( spl3_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f62,plain,
    ( spl3_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f109,plain,
    ( spl3_11
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f156,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_11 ),
    inference(resolution,[],[f110,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f110,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f155,plain,
    ( spl3_18
    | spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f152,f144,f136,f149])).

fof(f149,plain,
    ( spl3_18
  <=> v1_xboole_0(k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f136,plain,
    ( spl3_15
  <=> v1_zfmisc_1(k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f144,plain,
    ( spl3_17
  <=> m1_subset_1(sK1,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f152,plain,
    ( v1_zfmisc_1(k1_tarski(sK1))
    | v1_xboole_0(k1_tarski(sK1))
    | ~ spl3_17 ),
    inference(resolution,[],[f145,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_tarski(X0))
      | v1_zfmisc_1(k1_tarski(X0))
      | v1_xboole_0(k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f40,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) != X0
      | v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

% (23593)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f30,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f145,plain,
    ( m1_subset_1(sK1,k1_tarski(sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f151,plain,
    ( spl3_5
    | ~ spl3_3
    | ~ spl3_18
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f130,f120,f149,f62,f70])).

fof(f120,plain,
    ( spl3_12
  <=> k2_struct_0(sK0) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f130,plain,
    ( ~ v1_xboole_0(k1_tarski(sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_12 ),
    inference(superposition,[],[f43,f121])).

fof(f121,plain,
    ( k2_struct_0(sK0) = k1_tarski(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f120])).

fof(f146,plain,
    ( spl3_17
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f129,f120,f85,f144])).

fof(f85,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f129,plain,
    ( m1_subset_1(sK1,k1_tarski(sK1))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(superposition,[],[f86,f121])).

fof(f86,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f138,plain,
    ( ~ spl3_15
    | spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f127,f120,f92,f136])).

fof(f92,plain,
    ( spl3_9
  <=> v1_zfmisc_1(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f127,plain,
    ( ~ v1_zfmisc_1(k1_tarski(sK1))
    | spl3_9
    | ~ spl3_12 ),
    inference(superposition,[],[f93,f121])).

fof(f93,plain,
    ( ~ v1_zfmisc_1(k2_struct_0(sK0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f122,plain,
    ( spl3_11
    | ~ spl3_8
    | spl3_12
    | spl3_10 ),
    inference(avatar_split_clause,[],[f118,f105,f120,f85,f109])).

fof(f105,plain,
    ( spl3_10
  <=> v1_subset_1(k1_tarski(sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f118,plain,
    ( k2_struct_0(sK0) = k1_tarski(sK1)
    | ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK0))
    | spl3_10 ),
    inference(resolution,[],[f115,f106])).

fof(f106,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),k2_struct_0(sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k1_tarski(X0),X1)
      | k1_tarski(X0) = X1
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f98,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_subset_1(k1_tarski(X1),X0)
      | k1_tarski(X1) = X0 ) ),
    inference(resolution,[],[f50,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f111,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | spl3_11
    | spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f103,f75,f54,f109,f85,f105])).

fof(f54,plain,
    ( spl3_1
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f75,plain,
    ( spl3_6
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f103,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ v1_subset_1(k1_tarski(sK1),k2_struct_0(sK0))
    | spl3_1
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f102,f76])).

fof(f76,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f102,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ v1_subset_1(k1_tarski(sK1),k2_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f101,f76])).

fof(f101,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f99,f76])).

fof(f99,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl3_1 ),
    inference(superposition,[],[f55,f51])).

fof(f55,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f94,plain,
    ( spl3_4
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f88,f75,f92,f62,f66])).

fof(f66,plain,
    ( spl3_4
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f88,plain,
    ( ~ v1_zfmisc_1(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ spl3_6 ),
    inference(superposition,[],[f42,f76])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f87,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f79,f75,f58,f85])).

fof(f58,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f79,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(superposition,[],[f59,f76])).

fof(f59,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f77,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f73,f62,f75])).

fof(f73,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f41,f63])).

fof(f63,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f72,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f33,f70])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_struct_0(sK0)
    & ~ v7_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_struct_0(sK0)
      & ~ v7_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

% (23591)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (23584)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (23587)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (23594)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

fof(f68,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f34,f66])).

fof(f34,plain,(
    ~ v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f36,f58])).

fof(f36,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f37,f54])).

fof(f37,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (23583)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.46  % (23581)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.46  % (23585)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.47  % (23585)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f160,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f72,f77,f87,f94,f111,f122,f138,f146,f151,f155,f159])).
% 0.19/0.47  fof(f159,plain,(
% 0.19/0.47    spl3_5 | ~spl3_3 | ~spl3_11),
% 0.19/0.47    inference(avatar_split_clause,[],[f156,f109,f62,f70])).
% 0.19/0.47  fof(f70,plain,(
% 0.19/0.47    spl3_5 <=> v2_struct_0(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    spl3_3 <=> l1_struct_0(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.47  fof(f109,plain,(
% 0.19/0.47    spl3_11 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.47  fof(f156,plain,(
% 0.19/0.47    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_11),
% 0.19/0.47    inference(resolution,[],[f110,f43])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.19/0.47  fof(f110,plain,(
% 0.19/0.47    v1_xboole_0(k2_struct_0(sK0)) | ~spl3_11),
% 0.19/0.47    inference(avatar_component_clause,[],[f109])).
% 0.19/0.47  fof(f155,plain,(
% 0.19/0.47    spl3_18 | spl3_15 | ~spl3_17),
% 0.19/0.47    inference(avatar_split_clause,[],[f152,f144,f136,f149])).
% 0.19/0.47  fof(f149,plain,(
% 0.19/0.47    spl3_18 <=> v1_xboole_0(k1_tarski(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.19/0.47  fof(f136,plain,(
% 0.19/0.47    spl3_15 <=> v1_zfmisc_1(k1_tarski(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.47  fof(f144,plain,(
% 0.19/0.47    spl3_17 <=> m1_subset_1(sK1,k1_tarski(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.19/0.47  fof(f152,plain,(
% 0.19/0.47    v1_zfmisc_1(k1_tarski(sK1)) | v1_xboole_0(k1_tarski(sK1)) | ~spl3_17),
% 0.19/0.47    inference(resolution,[],[f145,f116])).
% 0.19/0.47  fof(f116,plain,(
% 0.19/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_tarski(X0)) | v1_zfmisc_1(k1_tarski(X0)) | v1_xboole_0(k1_tarski(X0))) )),
% 0.19/0.47    inference(equality_resolution,[],[f114])).
% 0.19/0.47  fof(f114,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k1_tarski(X1) != X0 | v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f113])).
% 0.19/0.47  fof(f113,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k1_tarski(X1) != X0 | v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.47    inference(superposition,[],[f40,f51])).
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.47    inference(flattening,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) != X0 | v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f30])).
% 0.19/0.47  % (23593)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.19/0.47    inference(rectify,[],[f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.19/0.47    inference(nnf_transformation,[],[f13])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.19/0.47  fof(f145,plain,(
% 0.19/0.47    m1_subset_1(sK1,k1_tarski(sK1)) | ~spl3_17),
% 0.19/0.47    inference(avatar_component_clause,[],[f144])).
% 0.19/0.47  fof(f151,plain,(
% 0.19/0.47    spl3_5 | ~spl3_3 | ~spl3_18 | ~spl3_12),
% 0.19/0.47    inference(avatar_split_clause,[],[f130,f120,f149,f62,f70])).
% 0.19/0.47  fof(f120,plain,(
% 0.19/0.47    spl3_12 <=> k2_struct_0(sK0) = k1_tarski(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.47  fof(f130,plain,(
% 0.19/0.47    ~v1_xboole_0(k1_tarski(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_12),
% 0.19/0.47    inference(superposition,[],[f43,f121])).
% 0.19/0.47  fof(f121,plain,(
% 0.19/0.47    k2_struct_0(sK0) = k1_tarski(sK1) | ~spl3_12),
% 0.19/0.47    inference(avatar_component_clause,[],[f120])).
% 0.19/0.47  fof(f146,plain,(
% 0.19/0.47    spl3_17 | ~spl3_8 | ~spl3_12),
% 0.19/0.47    inference(avatar_split_clause,[],[f129,f120,f85,f144])).
% 0.19/0.47  fof(f85,plain,(
% 0.19/0.47    spl3_8 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.47  fof(f129,plain,(
% 0.19/0.47    m1_subset_1(sK1,k1_tarski(sK1)) | (~spl3_8 | ~spl3_12)),
% 0.19/0.47    inference(superposition,[],[f86,f121])).
% 0.19/0.47  fof(f86,plain,(
% 0.19/0.47    m1_subset_1(sK1,k2_struct_0(sK0)) | ~spl3_8),
% 0.19/0.47    inference(avatar_component_clause,[],[f85])).
% 0.19/0.47  fof(f138,plain,(
% 0.19/0.47    ~spl3_15 | spl3_9 | ~spl3_12),
% 0.19/0.47    inference(avatar_split_clause,[],[f127,f120,f92,f136])).
% 0.19/0.47  fof(f92,plain,(
% 0.19/0.47    spl3_9 <=> v1_zfmisc_1(k2_struct_0(sK0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.47  fof(f127,plain,(
% 0.19/0.47    ~v1_zfmisc_1(k1_tarski(sK1)) | (spl3_9 | ~spl3_12)),
% 0.19/0.47    inference(superposition,[],[f93,f121])).
% 0.19/0.47  fof(f93,plain,(
% 0.19/0.47    ~v1_zfmisc_1(k2_struct_0(sK0)) | spl3_9),
% 0.19/0.47    inference(avatar_component_clause,[],[f92])).
% 0.19/0.47  fof(f122,plain,(
% 0.19/0.47    spl3_11 | ~spl3_8 | spl3_12 | spl3_10),
% 0.19/0.47    inference(avatar_split_clause,[],[f118,f105,f120,f85,f109])).
% 0.19/0.47  fof(f105,plain,(
% 0.19/0.47    spl3_10 <=> v1_subset_1(k1_tarski(sK1),k2_struct_0(sK0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.47  fof(f118,plain,(
% 0.19/0.47    k2_struct_0(sK0) = k1_tarski(sK1) | ~m1_subset_1(sK1,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0)) | spl3_10),
% 0.19/0.47    inference(resolution,[],[f115,f106])).
% 0.19/0.47  fof(f106,plain,(
% 0.19/0.47    ~v1_subset_1(k1_tarski(sK1),k2_struct_0(sK0)) | spl3_10),
% 0.19/0.47    inference(avatar_component_clause,[],[f105])).
% 0.19/0.47  fof(f115,plain,(
% 0.19/0.47    ( ! [X0,X1] : (v1_subset_1(k1_tarski(X0),X1) | k1_tarski(X0) = X1 | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 0.19/0.47    inference(resolution,[],[f98,f44])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.19/0.47    inference(nnf_transformation,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.47  fof(f98,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_subset_1(k1_tarski(X1),X0) | k1_tarski(X1) = X0) )),
% 0.19/0.47    inference(resolution,[],[f50,f48])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.47    inference(nnf_transformation,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.19/0.47  fof(f111,plain,(
% 0.19/0.47    ~spl3_10 | ~spl3_8 | spl3_11 | spl3_1 | ~spl3_6),
% 0.19/0.47    inference(avatar_split_clause,[],[f103,f75,f54,f109,f85,f105])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    spl3_1 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    spl3_6 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.47  fof(f103,plain,(
% 0.19/0.47    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k2_struct_0(sK0)) | ~v1_subset_1(k1_tarski(sK1),k2_struct_0(sK0)) | (spl3_1 | ~spl3_6)),
% 0.19/0.47    inference(forward_demodulation,[],[f102,f76])).
% 0.19/0.47  fof(f76,plain,(
% 0.19/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_6),
% 0.19/0.47    inference(avatar_component_clause,[],[f75])).
% 0.19/0.47  fof(f102,plain,(
% 0.19/0.47    ~m1_subset_1(sK1,k2_struct_0(sK0)) | ~v1_subset_1(k1_tarski(sK1),k2_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (spl3_1 | ~spl3_6)),
% 0.19/0.47    inference(forward_demodulation,[],[f101,f76])).
% 0.19/0.47  fof(f101,plain,(
% 0.19/0.47    ~v1_subset_1(k1_tarski(sK1),k2_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (spl3_1 | ~spl3_6)),
% 0.19/0.47    inference(forward_demodulation,[],[f99,f76])).
% 0.19/0.47  fof(f99,plain,(
% 0.19/0.47    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl3_1),
% 0.19/0.47    inference(superposition,[],[f55,f51])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl3_1),
% 0.19/0.47    inference(avatar_component_clause,[],[f54])).
% 0.19/0.47  fof(f94,plain,(
% 0.19/0.47    spl3_4 | ~spl3_3 | ~spl3_9 | ~spl3_6),
% 0.19/0.47    inference(avatar_split_clause,[],[f88,f75,f92,f62,f66])).
% 0.19/0.47  fof(f66,plain,(
% 0.19/0.47    spl3_4 <=> v7_struct_0(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.47  fof(f88,plain,(
% 0.19/0.47    ~v1_zfmisc_1(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v7_struct_0(sK0) | ~spl3_6),
% 0.19/0.47    inference(superposition,[],[f42,f76])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.19/0.47  fof(f87,plain,(
% 0.19/0.47    spl3_8 | ~spl3_2 | ~spl3_6),
% 0.19/0.47    inference(avatar_split_clause,[],[f79,f75,f58,f85])).
% 0.19/0.47  fof(f58,plain,(
% 0.19/0.47    spl3_2 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.47  fof(f79,plain,(
% 0.19/0.47    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl3_2 | ~spl3_6)),
% 0.19/0.47    inference(superposition,[],[f59,f76])).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_2),
% 0.19/0.47    inference(avatar_component_clause,[],[f58])).
% 0.19/0.47  fof(f77,plain,(
% 0.19/0.47    spl3_6 | ~spl3_3),
% 0.19/0.47    inference(avatar_split_clause,[],[f73,f62,f75])).
% 0.19/0.47  fof(f73,plain,(
% 0.19/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_3),
% 0.19/0.47    inference(resolution,[],[f41,f63])).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    l1_struct_0(sK0) | ~spl3_3),
% 0.19/0.47    inference(avatar_component_clause,[],[f62])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.47  fof(f72,plain,(
% 0.19/0.47    ~spl3_5),
% 0.19/0.47    inference(avatar_split_clause,[],[f33,f70])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ~v2_struct_0(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v7_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25,f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v7_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f11])).
% 0.19/0.47  fof(f11,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f10])).
% 0.19/0.48  % (23591)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.48  % (23584)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.48  % (23587)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.48  % (23594)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.49  fof(f10,negated_conjecture,(
% 0.19/0.49    ~! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.19/0.49    inference(negated_conjecture,[],[f9])).
% 0.19/0.49  fof(f9,conjecture,(
% 0.19/0.49    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).
% 0.19/0.49  fof(f68,plain,(
% 0.19/0.49    ~spl3_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f34,f66])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ~v7_struct_0(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f26])).
% 0.19/0.49  fof(f64,plain,(
% 0.19/0.49    spl3_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f35,f62])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    l1_struct_0(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f26])).
% 0.19/0.49  fof(f60,plain,(
% 0.19/0.49    spl3_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f36,f58])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.49    inference(cnf_transformation,[],[f26])).
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    ~spl3_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f37,f54])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.19/0.49    inference(cnf_transformation,[],[f26])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (23585)------------------------------
% 0.19/0.49  % (23585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (23585)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (23585)Memory used [KB]: 10618
% 0.19/0.49  % (23585)Time elapsed: 0.075 s
% 0.19/0.49  % (23585)------------------------------
% 0.19/0.49  % (23585)------------------------------
% 0.19/0.49  % (23578)Success in time 0.135 s
%------------------------------------------------------------------------------
