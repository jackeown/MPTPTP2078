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
% DateTime   : Thu Dec  3 13:22:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 245 expanded)
%              Number of leaves         :   28 ( 119 expanded)
%              Depth                    :    9
%              Number of atoms          :  465 (1177 expanded)
%              Number of equality atoms :   21 (  89 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7327)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f86,f105,f114,f121,f128,f138,f147,f154,f218,f231,f232,f234])).

fof(f234,plain,
    ( ~ spl4_25
    | ~ spl4_28
    | ~ spl4_11
    | spl4_26 ),
    inference(avatar_split_clause,[],[f233,f215,f112,f228,f211])).

% (7313)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f211,plain,
    ( spl4_25
  <=> m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f228,plain,
    ( spl4_28
  <=> v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f112,plain,
    ( spl4_11
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f215,plain,
    ( spl4_26
  <=> v3_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f233,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_11
    | spl4_26 ),
    inference(resolution,[],[f217,f113])).

fof(f113,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f217,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)
    | spl4_26 ),
    inference(avatar_component_clause,[],[f215])).

fof(f232,plain,
    ( spl4_25
    | ~ spl4_3
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f225,f151,f68,f211])).

% (7325)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
fof(f68,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f151,plain,
    ( spl4_17
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f225,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f70,f153,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f153,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f70,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f231,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f226,f151,f78,f68,f228])).

fof(f78,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f226,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f80,f70,f153,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f80,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f218,plain,
    ( spl4_6
    | ~ spl4_5
    | ~ spl4_3
    | ~ spl4_2
    | ~ spl4_25
    | ~ spl4_26
    | spl4_1
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f209,f144,f58,f215,f211,f63,f68,f78,f83])).

fof(f83,plain,
    ( spl4_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f63,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f58,plain,
    ( spl4_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f144,plain,
    ( spl4_16
  <=> k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f209,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v3_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_16 ),
    inference(trivial_inequality_removal,[],[f208])).

fof(f208,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0)
    | ~ v3_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_16 ),
    inference(superposition,[],[f47,f146])).

fof(f146,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
      | v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).

fof(f154,plain,
    ( spl4_17
    | spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f149,f135,f118,f151])).

fof(f118,plain,
    ( spl4_12
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f135,plain,
    ( spl4_15
  <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f149,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_12
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f120,f137,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f137,plain,
    ( m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f120,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f147,plain,
    ( ~ spl4_15
    | spl4_16
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f141,f125,f144,f135])).

fof(f125,plain,
    ( spl4_13
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f141,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_13 ),
    inference(resolution,[],[f127,f42])).

fof(f42,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & ! [X2] :
        ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & ! [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & ! [X2] :
            ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(sK1,sK0)
      & ! [X2] :
          ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          | ~ r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tex_2)).

fof(f127,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f138,plain,
    ( spl4_15
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f133,f83,f78,f68,f63,f58,f135])).

fof(f133,plain,
    ( m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f85,f80,f70,f60,f65,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f60,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f85,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f128,plain,
    ( spl4_13
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f122,f83,f78,f68,f63,f58,f125])).

fof(f122,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f85,f80,f70,f60,f65,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f121,plain,
    ( ~ spl4_12
    | ~ spl4_2
    | spl4_9 ),
    inference(avatar_split_clause,[],[f115,f102,f63,f118])).

fof(f102,plain,
    ( spl4_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f115,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_2
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f65,f104,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f104,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f114,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_11
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f110,f78,f112,f73,f68])).

fof(f73,plain,
    ( spl4_4
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(X0,sK0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f52,f80])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & v4_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f105,plain,
    ( ~ spl4_9
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f99,f83,f78,f68,f63,f58,f102])).

fof(f99,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f85,f80,f70,f60,f65,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f86,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f73])).

fof(f39,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f40,f68])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f63])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f43,f58])).

fof(f43,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:12:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (7312)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.54  % (7310)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.54  % (7311)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.54  % (7309)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.54  % (7309)Refutation not found, incomplete strategy% (7309)------------------------------
% 0.22/0.54  % (7309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7306)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.54  % (7314)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.55  % (7309)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (7309)Memory used [KB]: 10618
% 0.22/0.55  % (7309)Time elapsed: 0.102 s
% 0.22/0.55  % (7309)------------------------------
% 0.22/0.55  % (7309)------------------------------
% 0.22/0.55  % (7307)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.55  % (7329)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.55  % (7308)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.55  % (7321)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.56  % (7326)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.56  % (7312)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  % (7327)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.56  fof(f235,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f86,f105,f114,f121,f128,f138,f147,f154,f218,f231,f232,f234])).
% 0.22/0.56  fof(f234,plain,(
% 0.22/0.56    ~spl4_25 | ~spl4_28 | ~spl4_11 | spl4_26),
% 0.22/0.56    inference(avatar_split_clause,[],[f233,f215,f112,f228,f211])).
% 0.22/0.56  % (7313)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  fof(f211,plain,(
% 0.22/0.56    spl4_25 <=> m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.56  fof(f228,plain,(
% 0.22/0.56    spl4_28 <=> v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    spl4_11 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.56  fof(f215,plain,(
% 0.22/0.56    spl4_26 <=> v3_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.56  fof(f233,plain,(
% 0.22/0.56    ~v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_11 | spl4_26)),
% 0.22/0.56    inference(resolution,[],[f217,f113])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_11),
% 0.22/0.56    inference(avatar_component_clause,[],[f112])).
% 0.22/0.56  fof(f217,plain,(
% 0.22/0.56    ~v3_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0) | spl4_26),
% 0.22/0.56    inference(avatar_component_clause,[],[f215])).
% 0.22/0.56  fof(f232,plain,(
% 0.22/0.56    spl4_25 | ~spl4_3 | ~spl4_17),
% 0.22/0.56    inference(avatar_split_clause,[],[f225,f151,f68,f211])).
% 0.22/0.56  % (7325)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    spl4_3 <=> l1_pre_topc(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.56  fof(f151,plain,(
% 0.22/0.56    spl4_17 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.56  fof(f225,plain,(
% 0.22/0.56    m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_3 | ~spl4_17)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f70,f153,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.56  fof(f153,plain,(
% 0.22/0.56    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_17),
% 0.22/0.56    inference(avatar_component_clause,[],[f151])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    l1_pre_topc(sK0) | ~spl4_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f68])).
% 0.22/0.56  fof(f231,plain,(
% 0.22/0.56    spl4_28 | ~spl4_3 | ~spl4_5 | ~spl4_17),
% 0.22/0.56    inference(avatar_split_clause,[],[f226,f151,f78,f68,f228])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    spl4_5 <=> v2_pre_topc(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.56  fof(f226,plain,(
% 0.22/0.56    v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0) | (~spl4_3 | ~spl4_5 | ~spl4_17)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f80,f70,f153,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    v2_pre_topc(sK0) | ~spl4_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f78])).
% 0.22/0.56  fof(f218,plain,(
% 0.22/0.56    spl4_6 | ~spl4_5 | ~spl4_3 | ~spl4_2 | ~spl4_25 | ~spl4_26 | spl4_1 | ~spl4_16),
% 0.22/0.56    inference(avatar_split_clause,[],[f209,f144,f58,f215,f211,f63,f68,f78,f83])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    spl4_6 <=> v2_struct_0(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    spl4_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    spl4_1 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.56  fof(f144,plain,(
% 0.22/0.56    spl4_16 <=> k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.56  fof(f209,plain,(
% 0.22/0.56    v2_tex_2(sK1,sK0) | ~v3_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_16),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f208])).
% 0.22/0.56  fof(f208,plain,(
% 0.22/0.56    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) | v2_tex_2(sK1,sK0) | ~v3_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_16),
% 0.22/0.56    inference(superposition,[],[f47,f146])).
% 0.22/0.56  fof(f146,plain,(
% 0.22/0.56    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) | ~spl4_16),
% 0.22/0.56    inference(avatar_component_clause,[],[f144])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) | v2_tex_2(X1,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) | ? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))) => v2_tex_2(X1,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).
% 0.22/0.56  fof(f154,plain,(
% 0.22/0.56    spl4_17 | spl4_12 | ~spl4_15),
% 0.22/0.56    inference(avatar_split_clause,[],[f149,f135,f118,f151])).
% 0.22/0.56  fof(f118,plain,(
% 0.22/0.56    spl4_12 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    spl4_15 <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.56  fof(f149,plain,(
% 0.22/0.56    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_12 | ~spl4_15)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f120,f137,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.56    inference(flattening,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.56  fof(f137,plain,(
% 0.22/0.56    m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | ~spl4_15),
% 0.22/0.56    inference(avatar_component_clause,[],[f135])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_12),
% 0.22/0.56    inference(avatar_component_clause,[],[f118])).
% 0.22/0.56  fof(f147,plain,(
% 0.22/0.56    ~spl4_15 | spl4_16 | ~spl4_13),
% 0.22/0.56    inference(avatar_split_clause,[],[f141,f125,f144,f135])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    spl4_13 <=> r2_hidden(sK2(sK0,sK1),sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.56  fof(f141,plain,(
% 0.22/0.56    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) | ~m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | ~spl4_13),
% 0.22/0.56    inference(resolution,[],[f127,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X2] : (~r2_hidden(X2,sK1) | k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    (~v2_tex_2(sK1,sK0) & ! [X2] : (k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_hidden(X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f29,f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & ! [X2] : (k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ? [X1] : (~v2_tex_2(X1,sK0) & ! [X2] : (k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(sK1,sK0) & ! [X2] : (k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_hidden(X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : ((~v2_tex_2(X1,X0) & ! [X2] : ((k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,negated_conjecture,(
% 0.22/0.56    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 0.22/0.56    inference(negated_conjecture,[],[f9])).
% 0.22/0.56  fof(f9,conjecture,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tex_2)).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    r2_hidden(sK2(sK0,sK1),sK1) | ~spl4_13),
% 0.22/0.56    inference(avatar_component_clause,[],[f125])).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    spl4_15 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | spl4_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f133,f83,f78,f68,f63,f58,f135])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | spl4_6)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f85,f80,f70,f60,f65,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f63])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ~v2_tex_2(sK1,sK0) | spl4_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f58])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    ~v2_struct_0(sK0) | spl4_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f83])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    spl4_13 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | spl4_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f122,f83,f78,f68,f63,f58,f125])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    r2_hidden(sK2(sK0,sK1),sK1) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | spl4_6)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f85,f80,f70,f60,f65,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v2_struct_0(X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_tex_2(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    ~spl4_12 | ~spl4_2 | spl4_9),
% 0.22/0.56    inference(avatar_split_clause,[],[f115,f102,f63,f118])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    spl4_9 <=> v1_xboole_0(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.56  fof(f115,plain,(
% 0.22/0.56    ~v1_xboole_0(u1_struct_0(sK0)) | (~spl4_2 | spl4_9)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f65,f104,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    ~v1_xboole_0(sK1) | spl4_9),
% 0.22/0.56    inference(avatar_component_clause,[],[f102])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    ~spl4_3 | ~spl4_4 | spl4_11 | ~spl4_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f110,f78,f112,f73,f68])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    spl4_4 <=> v3_tdlat_3(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v3_pre_topc(X0,sK0)) ) | ~spl4_5),
% 0.22/0.56    inference(resolution,[],[f52,f80])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~v2_pre_topc(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v3_pre_topc(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(rectify,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    ~spl4_9 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | spl4_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f99,f83,f78,f68,f63,f58,f102])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    ~v1_xboole_0(sK1) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | spl4_6)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f85,f80,f70,f60,f65,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_tex_2(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    ~spl4_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f37,f83])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ~v2_struct_0(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    spl4_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f38,f78])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    v2_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    spl4_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f39,f73])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    v3_tdlat_3(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    spl4_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f40,f68])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    l1_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    spl4_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f41,f63])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ~spl4_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f43,f58])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ~v2_tex_2(sK1,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (7312)------------------------------
% 0.22/0.56  % (7312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (7312)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (7312)Memory used [KB]: 10746
% 0.22/0.56  % (7312)Time elapsed: 0.127 s
% 0.22/0.56  % (7312)------------------------------
% 0.22/0.56  % (7312)------------------------------
% 0.22/0.56  % (7305)Success in time 0.198 s
%------------------------------------------------------------------------------
