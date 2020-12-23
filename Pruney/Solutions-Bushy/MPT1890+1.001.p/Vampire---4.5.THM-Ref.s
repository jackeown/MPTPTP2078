%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1890+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 250 expanded)
%              Number of leaves         :   18 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  332 (1432 expanded)
%              Number of equality atoms :   17 ( 130 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f152,f157,f159,f166,f185,f188,f193,f201,f209,f213,f215])).

fof(f215,plain,(
    ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl3_11 ),
    inference(resolution,[],[f175,f24])).

fof(f24,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f175,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_11
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f213,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl3_1 ),
    inference(resolution,[],[f162,f203])).

fof(f203,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f84])).

fof(f84,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f83,f23])).

% (7506)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X10] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X10))
      | ~ v1_xboole_0(X10) ) ),
    inference(global_subsumption,[],[f25,f26,f27,f28,f24,f76])).

fof(f76,plain,(
    ! [X10] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X10))
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | v2_struct_0(sK0)
      | v2_tex_2(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_xboole_0(X10) ) ),
    inference(resolution,[],[f60,f23])).

fof(f60,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | ~ l1_pre_topc(X2)
      | ~ v3_tdlat_3(X2)
      | v2_struct_0(X2)
      | v2_tex_2(X3,X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f31,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tex_2)).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f162,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f209,plain,(
    ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f208])).

% (7507)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
fof(f208,plain,
    ( $false
    | ~ spl3_12 ),
    inference(resolution,[],[f178,f25])).

fof(f178,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl3_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f201,plain,
    ( ~ spl3_9
    | ~ spl3_8
    | spl3_6 ),
    inference(avatar_split_clause,[],[f199,f136,f147,f150])).

fof(f150,plain,
    ( spl3_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f147,plain,
    ( spl3_8
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f136,plain,
    ( spl3_6
  <=> m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f199,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_6 ),
    inference(resolution,[],[f137,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

% (7519)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f137,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f193,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl3_13 ),
    inference(resolution,[],[f181,f23])).

fof(f181,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl3_13
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f188,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl3_14 ),
    inference(resolution,[],[f184,f27])).

fof(f184,plain,
    ( ~ v3_tdlat_3(sK0)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl3_14
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f185,plain,
    ( spl3_11
    | spl3_12
    | ~ spl3_13
    | ~ spl3_9
    | ~ spl3_14
    | ~ spl3_7
    | spl3_10 ),
    inference(avatar_split_clause,[],[f171,f164,f144,f183,f150,f180,f177,f174])).

fof(f144,plain,
    ( spl3_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f164,plain,
    ( spl3_10
  <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f171,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0)
    | spl3_10 ),
    inference(resolution,[],[f165,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f165,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f166,plain,
    ( spl3_1
    | ~ spl3_10
    | spl3_8 ),
    inference(avatar_split_clause,[],[f160,f147,f164,f39])).

fof(f160,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl3_8 ),
    inference(resolution,[],[f148,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f148,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f159,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f151,f28])).

fof(f151,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f157,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f145,f26])).

fof(f145,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f152,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_5 ),
    inference(avatar_split_clause,[],[f142,f133,f150,f147,f144])).

fof(f133,plain,
    ( spl3_5
  <=> v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f142,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | spl3_5 ),
    inference(resolution,[],[f134,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f134,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f138,plain,
    ( ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f131,f136,f133])).

fof(f131,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0) ),
    inference(global_subsumption,[],[f25,f26,f27,f28,f24,f23,f130])).

fof(f130,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f129])).

fof(f129,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(superposition,[],[f29,f98])).

fof(f98,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) ),
    inference(global_subsumption,[],[f25,f26,f27,f28,f24,f96])).

fof(f96,plain,
    ( ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0)
    | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) ),
    inference(resolution,[],[f63,f23])).

fof(f63,plain,(
    ! [X6] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ v3_tdlat_3(X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | v2_tex_2(sK1,X6)
      | k6_domain_1(u1_struct_0(sK0),sK2(X6,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(X6,sK1)))) ) ),
    inference(global_subsumption,[],[f61])).

fof(f61,plain,(
    ! [X5] :
      ( ~ v2_pre_topc(X5)
      | ~ v3_tdlat_3(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X5)))
      | v2_struct_0(X5)
      | v2_tex_2(sK1,X5)
      | k6_domain_1(u1_struct_0(sK0),sK2(X5,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(X5,sK1)))) ) ),
    inference(resolution,[],[f31,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k6_domain_1(u1_struct_0(sK0),X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK1)
      | k6_domain_1(u1_struct_0(sK0),X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f46,f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,X1)
      | k6_domain_1(u1_struct_0(sK0),X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f22,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f22,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
