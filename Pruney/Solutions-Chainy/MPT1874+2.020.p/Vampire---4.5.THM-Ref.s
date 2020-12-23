%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 396 expanded)
%              Number of leaves         :   47 ( 175 expanded)
%              Depth                    :   11
%              Number of atoms          :  562 (1376 expanded)
%              Number of equality atoms :   90 ( 241 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f111,f116,f121,f126,f131,f136,f164,f222,f352,f359,f368,f556,f565,f595,f608,f997,f1013,f1144,f1168,f1178,f1188,f2359])).

fof(f2359,plain,
    ( spl6_119
    | ~ spl6_34
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f2353,f994,f349,f1185])).

fof(f1185,plain,
    ( spl6_119
  <=> m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).

fof(f349,plain,
    ( spl6_34
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f994,plain,
    ( spl6_98
  <=> k6_domain_1(sK1,sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f2353,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl6_34
    | ~ spl6_98 ),
    inference(superposition,[],[f2333,f996])).

fof(f996,plain,
    ( k6_domain_1(sK1,sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1)
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f994])).

fof(f2333,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(sK1))
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f626,f627])).

fof(f627,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(sK1,X0,sK1)
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f350,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f350,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f349])).

fof(f626,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(sK1,X0,sK1),k1_zfmisc_1(sK1))
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f350,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f1188,plain,
    ( ~ spl6_119
    | spl6_118 ),
    inference(avatar_split_clause,[],[f1183,f1174,f1185])).

fof(f1174,plain,
    ( spl6_118
  <=> r1_tarski(k6_domain_1(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f1183,plain,
    ( ~ m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1))
    | spl6_118 ),
    inference(unit_resulting_resolution,[],[f1176,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1176,plain,
    ( ~ r1_tarski(k6_domain_1(sK1,sK2),sK1)
    | spl6_118 ),
    inference(avatar_component_clause,[],[f1174])).

fof(f1178,plain,
    ( ~ spl6_118
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_100
    | spl6_117 ),
    inference(avatar_split_clause,[],[f1170,f1165,f1010,f133,f128,f123,f118,f113,f1174])).

fof(f113,plain,
    ( spl6_4
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f118,plain,
    ( spl6_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f123,plain,
    ( spl6_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f128,plain,
    ( spl6_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f133,plain,
    ( spl6_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1010,plain,
    ( spl6_100
  <=> m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f1165,plain,
    ( spl6_117
  <=> k6_domain_1(sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f1170,plain,
    ( ~ r1_tarski(k6_domain_1(sK1,sK2),sK1)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_100
    | spl6_117 ),
    inference(unit_resulting_resolution,[],[f135,f130,f125,f115,f120,f1012,f1167,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK4(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK4(X0,X1)))
                & r1_tarski(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK4(X0,X1)))
        & r1_tarski(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

% (4203)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(f1167,plain,
    ( k6_domain_1(sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(sK1,sK2)))
    | spl6_117 ),
    inference(avatar_component_clause,[],[f1165])).

fof(f1012,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f1010])).

fof(f120,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f115,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f125,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f130,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f135,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1168,plain,
    ( ~ spl6_117
    | spl6_1
    | ~ spl6_113 ),
    inference(avatar_split_clause,[],[f1158,f1141,f98,f1165])).

fof(f98,plain,
    ( spl6_1
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1141,plain,
    ( spl6_113
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k6_domain_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_113])])).

fof(f1158,plain,
    ( k6_domain_1(sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(sK1,sK2)))
    | spl6_1
    | ~ spl6_113 ),
    inference(backward_demodulation,[],[f100,f1143])).

fof(f1143,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k6_domain_1(sK1,sK2)
    | ~ spl6_113 ),
    inference(avatar_component_clause,[],[f1141])).

fof(f100,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f1144,plain,
    ( spl6_113
    | ~ spl6_17
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f1139,f218,f213,f1141])).

fof(f213,plain,
    ( spl6_17
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_domain_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f218,plain,
    ( spl6_18
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f1139,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k6_domain_1(sK1,sK2)
    | ~ spl6_17
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f220,f215])).

fof(f215,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_domain_1(sK1,sK2)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f213])).

fof(f220,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f218])).

fof(f1013,plain,
    ( spl6_100
    | ~ spl6_5
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f1003,f994,f118,f1010])).

fof(f1003,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5
    | ~ spl6_98 ),
    inference(superposition,[],[f372,f996])).

fof(f372,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f175,f178])).

fof(f178,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f120,f81])).

fof(f175,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f120,f80])).

fof(f997,plain,
    ( spl6_98
    | ~ spl6_17
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f992,f605,f213,f994])).

fof(f605,plain,
    ( spl6_62
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f992,plain,
    ( k6_domain_1(sK1,sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1)
    | ~ spl6_17
    | ~ spl6_62 ),
    inference(backward_demodulation,[],[f607,f215])).

fof(f607,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f605])).

fof(f608,plain,
    ( spl6_62
    | ~ spl6_5
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f603,f356,f118,f605])).

fof(f356,plain,
    ( spl6_35
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f603,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1)
    | ~ spl6_5
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f358,f472])).

fof(f472,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f186,f178])).

fof(f186,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f120,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f358,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK2))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f356])).

fof(f595,plain,
    ( spl6_34
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f588,f494,f349])).

fof(f494,plain,
    ( spl6_48
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f588,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_48 ),
    inference(resolution,[],[f495,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f495,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f494])).

fof(f565,plain,
    ( spl6_48
    | ~ spl6_5
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f564,f118,f118,f494])).

fof(f564,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK1)
    | ~ spl6_5 ),
    inference(duplicate_literal_removal,[],[f562])).

fof(f562,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f198,f197])).

fof(f197,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(u1_struct_0(sK0),sK1,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f74,f120])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK5(X0,X1,X2),X2)
            & r2_hidden(sK5(X0,X1,X2),X1)
            & m1_subset_1(sK5(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(u1_struct_0(sK0),sK1,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK1,X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f75,f120])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f556,plain,
    ( spl6_10
    | spl6_17
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f554,f155,f213,f151])).

fof(f151,plain,
    ( spl6_10
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f155,plain,
    ( spl6_11
  <=> m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f554,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_domain_1(sK1,sK2)
    | v1_xboole_0(sK1)
    | ~ spl6_11 ),
    inference(resolution,[],[f157,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f76,f94])).

fof(f94,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f93])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f85,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f86,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f87,f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f157,plain,
    ( m1_subset_1(sK2,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f155])).

fof(f368,plain,
    ( ~ spl6_34
    | ~ spl6_2
    | spl6_11 ),
    inference(avatar_split_clause,[],[f363,f155,f103,f349])).

fof(f103,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f363,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_2
    | spl6_11 ),
    inference(unit_resulting_resolution,[],[f105,f156,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f156,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f155])).

fof(f105,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f359,plain,
    ( spl6_35
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f353,f123,f118,f113,f108,f103,f356])).

fof(f108,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f353,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK2))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f125,f105,f115,f110,f120,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ) ),
    inference(definition_unfolding,[],[f63,f94])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2))
                & v4_pre_topc(sK3(X0,X1,X2),X0)
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2))
        & v4_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

fof(f110,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f352,plain,
    ( ~ spl6_34
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f312,f151,f103,f349])).

fof(f312,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f105,f153,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f153,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f222,plain,
    ( spl6_12
    | spl6_18
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f204,f108,f218,f161])).

fof(f161,plain,
    ( spl6_12
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f204,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f96,f110])).

fof(f164,plain,
    ( ~ spl6_12
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f159,f118,f103,f161])).

fof(f159,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f105,f120,f84])).

fof(f136,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f52,f133])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & r2_hidden(X2,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

fof(f131,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f53,f128])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f126,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f54,f123])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f121,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f55,f118])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f116,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f56,f113])).

fof(f56,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f111,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f57,f108])).

fof(f57,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f106,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f58,f103])).

fof(f58,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f59,f98])).

fof(f59,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:53:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (4193)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.45  % (4192)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.45  % (4190)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (4188)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.46  % (4198)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.46  % (4186)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (4189)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.46  % (4196)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.46  % (4201)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.46  % (4200)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (4195)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (4197)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (4199)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (4202)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (4194)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (4191)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (4187)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (4192)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f2360,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f101,f106,f111,f116,f121,f126,f131,f136,f164,f222,f352,f359,f368,f556,f565,f595,f608,f997,f1013,f1144,f1168,f1178,f1188,f2359])).
% 0.22/0.49  fof(f2359,plain,(
% 0.22/0.49    spl6_119 | ~spl6_34 | ~spl6_98),
% 0.22/0.49    inference(avatar_split_clause,[],[f2353,f994,f349,f1185])).
% 0.22/0.49  fof(f1185,plain,(
% 0.22/0.49    spl6_119 <=> m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).
% 0.22/0.49  fof(f349,plain,(
% 0.22/0.49    spl6_34 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.22/0.49  fof(f994,plain,(
% 0.22/0.49    spl6_98 <=> k6_domain_1(sK1,sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 0.22/0.49  fof(f2353,plain,(
% 0.22/0.49    m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1)) | (~spl6_34 | ~spl6_98)),
% 0.22/0.49    inference(superposition,[],[f2333,f996])).
% 0.22/0.49  fof(f996,plain,(
% 0.22/0.49    k6_domain_1(sK1,sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1) | ~spl6_98),
% 0.22/0.49    inference(avatar_component_clause,[],[f994])).
% 0.22/0.49  fof(f2333,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(sK1))) ) | ~spl6_34),
% 0.22/0.49    inference(backward_demodulation,[],[f626,f627])).
% 0.22/0.49  fof(f627,plain,(
% 0.22/0.49    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(sK1,X0,sK1)) ) | ~spl6_34),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f350,f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.49  fof(f350,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl6_34),
% 0.22/0.49    inference(avatar_component_clause,[],[f349])).
% 0.22/0.49  fof(f626,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k9_subset_1(sK1,X0,sK1),k1_zfmisc_1(sK1))) ) | ~spl6_34),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f350,f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.22/0.49  fof(f1188,plain,(
% 0.22/0.49    ~spl6_119 | spl6_118),
% 0.22/0.49    inference(avatar_split_clause,[],[f1183,f1174,f1185])).
% 0.22/0.49  fof(f1174,plain,(
% 0.22/0.49    spl6_118 <=> r1_tarski(k6_domain_1(sK1,sK2),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).
% 0.22/0.49  fof(f1183,plain,(
% 0.22/0.49    ~m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1)) | spl6_118),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f1176,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f1176,plain,(
% 0.22/0.49    ~r1_tarski(k6_domain_1(sK1,sK2),sK1) | spl6_118),
% 0.22/0.49    inference(avatar_component_clause,[],[f1174])).
% 0.22/0.49  fof(f1178,plain,(
% 0.22/0.49    ~spl6_118 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_8 | ~spl6_100 | spl6_117),
% 0.22/0.49    inference(avatar_split_clause,[],[f1170,f1165,f1010,f133,f128,f123,f118,f113,f1174])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    spl6_4 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    spl6_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    spl6_6 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    spl6_7 <=> v2_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    spl6_8 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.49  fof(f1010,plain,(
% 0.22/0.49    spl6_100 <=> m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).
% 0.22/0.49  fof(f1165,plain,(
% 0.22/0.49    spl6_117 <=> k6_domain_1(sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(sK1,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).
% 0.22/0.49  fof(f1170,plain,(
% 0.22/0.49    ~r1_tarski(k6_domain_1(sK1,sK2),sK1) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_8 | ~spl6_100 | spl6_117)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f135,f130,f125,f115,f120,f1012,f1167,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK4(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK4(X0,X1))) & r1_tarski(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK4(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK4(X0,X1))) & r1_tarski(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(rectify,[],[f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  % (4203)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 0.22/0.49  fof(f1167,plain,(
% 0.22/0.49    k6_domain_1(sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(sK1,sK2))) | spl6_117),
% 0.22/0.49    inference(avatar_component_clause,[],[f1165])).
% 0.22/0.49  fof(f1012,plain,(
% 0.22/0.49    m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_100),
% 0.22/0.49    inference(avatar_component_clause,[],[f1010])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f118])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    v2_tex_2(sK1,sK0) | ~spl6_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f113])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    l1_pre_topc(sK0) | ~spl6_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f123])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    v2_pre_topc(sK0) | ~spl6_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f128])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ~v2_struct_0(sK0) | spl6_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f133])).
% 0.22/0.49  fof(f1168,plain,(
% 0.22/0.49    ~spl6_117 | spl6_1 | ~spl6_113),
% 0.22/0.49    inference(avatar_split_clause,[],[f1158,f1141,f98,f1165])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl6_1 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f1141,plain,(
% 0.22/0.49    spl6_113 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k6_domain_1(sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_113])])).
% 0.22/0.49  fof(f1158,plain,(
% 0.22/0.49    k6_domain_1(sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(sK1,sK2))) | (spl6_1 | ~spl6_113)),
% 0.22/0.49    inference(backward_demodulation,[],[f100,f1143])).
% 0.22/0.49  fof(f1143,plain,(
% 0.22/0.49    k6_domain_1(u1_struct_0(sK0),sK2) = k6_domain_1(sK1,sK2) | ~spl6_113),
% 0.22/0.49    inference(avatar_component_clause,[],[f1141])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl6_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f98])).
% 0.22/0.49  fof(f1144,plain,(
% 0.22/0.49    spl6_113 | ~spl6_17 | ~spl6_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f1139,f218,f213,f1141])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    spl6_17 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_domain_1(sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    spl6_18 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.49  fof(f1139,plain,(
% 0.22/0.49    k6_domain_1(u1_struct_0(sK0),sK2) = k6_domain_1(sK1,sK2) | (~spl6_17 | ~spl6_18)),
% 0.22/0.49    inference(forward_demodulation,[],[f220,f215])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_domain_1(sK1,sK2) | ~spl6_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f213])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl6_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f218])).
% 0.22/0.49  fof(f1013,plain,(
% 0.22/0.49    spl6_100 | ~spl6_5 | ~spl6_98),
% 0.22/0.49    inference(avatar_split_clause,[],[f1003,f994,f118,f1010])).
% 0.22/0.49  fof(f1003,plain,(
% 0.22/0.49    m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_5 | ~spl6_98)),
% 0.22/0.49    inference(superposition,[],[f372,f996])).
% 0.22/0.49  fof(f372,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_5),
% 0.22/0.49    inference(backward_demodulation,[],[f175,f178])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)) ) | ~spl6_5),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f120,f81])).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_5),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f120,f80])).
% 0.22/0.49  fof(f997,plain,(
% 0.22/0.49    spl6_98 | ~spl6_17 | ~spl6_62),
% 0.22/0.49    inference(avatar_split_clause,[],[f992,f605,f213,f994])).
% 0.22/0.49  fof(f605,plain,(
% 0.22/0.49    spl6_62 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 0.22/0.49  fof(f992,plain,(
% 0.22/0.49    k6_domain_1(sK1,sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1) | (~spl6_17 | ~spl6_62)),
% 0.22/0.49    inference(backward_demodulation,[],[f607,f215])).
% 0.22/0.49  fof(f607,plain,(
% 0.22/0.49    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1) | ~spl6_62),
% 0.22/0.49    inference(avatar_component_clause,[],[f605])).
% 0.22/0.49  fof(f608,plain,(
% 0.22/0.49    spl6_62 | ~spl6_5 | ~spl6_35),
% 0.22/0.49    inference(avatar_split_clause,[],[f603,f356,f118,f605])).
% 0.22/0.49  fof(f356,plain,(
% 0.22/0.49    spl6_35 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.22/0.49  fof(f603,plain,(
% 0.22/0.49    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1) | (~spl6_5 | ~spl6_35)),
% 0.22/0.49    inference(forward_demodulation,[],[f358,f472])).
% 0.22/0.49  fof(f472,plain,(
% 0.22/0.49    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl6_5),
% 0.22/0.49    inference(forward_demodulation,[],[f186,f178])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl6_5),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f120,f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.22/0.49  fof(f358,plain,(
% 0.22/0.49    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK2)) | ~spl6_35),
% 0.22/0.49    inference(avatar_component_clause,[],[f356])).
% 0.22/0.49  fof(f595,plain,(
% 0.22/0.49    spl6_34 | ~spl6_48),
% 0.22/0.49    inference(avatar_split_clause,[],[f588,f494,f349])).
% 0.22/0.49  fof(f494,plain,(
% 0.22/0.49    spl6_48 <=> r1_tarski(sK1,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.22/0.49  fof(f588,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl6_48),
% 0.22/0.49    inference(resolution,[],[f495,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f51])).
% 0.22/0.49  fof(f495,plain,(
% 0.22/0.49    r1_tarski(sK1,sK1) | ~spl6_48),
% 0.22/0.49    inference(avatar_component_clause,[],[f494])).
% 0.22/0.49  fof(f565,plain,(
% 0.22/0.49    spl6_48 | ~spl6_5 | ~spl6_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f564,f118,f118,f494])).
% 0.22/0.49  fof(f564,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK1) | ~spl6_5),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f562])).
% 0.22/0.49  fof(f562,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK1) | ~spl6_5),
% 0.22/0.49    inference(resolution,[],[f198,f197])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK5(u1_struct_0(sK0),sK1,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | ~spl6_5),
% 0.22/0.49    inference(resolution,[],[f74,f120])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(flattening,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(sK5(u1_struct_0(sK0),sK1,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) ) | ~spl6_5),
% 0.22/0.49    inference(resolution,[],[f75,f120])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK5(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f50])).
% 0.22/0.49  fof(f556,plain,(
% 0.22/0.49    spl6_10 | spl6_17 | ~spl6_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f554,f155,f213,f151])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    spl6_10 <=> v1_xboole_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    spl6_11 <=> m1_subset_1(sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.49  fof(f554,plain,(
% 0.22/0.49    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_domain_1(sK1,sK2) | v1_xboole_0(sK1) | ~spl6_11),
% 0.22/0.49    inference(resolution,[],[f157,f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f76,f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f60,f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f68,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f79,f91])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f85,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f86,f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f87,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    m1_subset_1(sK2,sK1) | ~spl6_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f155])).
% 0.22/0.49  fof(f368,plain,(
% 0.22/0.49    ~spl6_34 | ~spl6_2 | spl6_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f363,f155,f103,f349])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    spl6_2 <=> r2_hidden(sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.49  fof(f363,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl6_2 | spl6_11)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f105,f156,f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    ~m1_subset_1(sK2,sK1) | spl6_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f155])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    r2_hidden(sK2,sK1) | ~spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f103])).
% 0.22/0.49  fof(f359,plain,(
% 0.22/0.49    spl6_35 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f353,f123,f118,f113,f108,f103,f356])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    spl6_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.49  fof(f353,plain,(
% 0.22/0.49    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK2)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f125,f105,f115,f110,f120,f95])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f63,f94])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) & v4_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) & v4_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f108])).
% 0.22/0.49  fof(f352,plain,(
% 0.22/0.49    ~spl6_34 | ~spl6_2 | ~spl6_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f312,f151,f103,f349])).
% 0.22/0.49  fof(f312,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl6_2 | ~spl6_10)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f105,f153,f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    v1_xboole_0(sK1) | ~spl6_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f151])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    spl6_12 | spl6_18 | ~spl6_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f204,f108,f218,f161])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    spl6_12 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    k6_domain_1(u1_struct_0(sK0),sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | v1_xboole_0(u1_struct_0(sK0)) | ~spl6_3),
% 0.22/0.49    inference(resolution,[],[f96,f110])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    ~spl6_12 | ~spl6_2 | ~spl6_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f159,f118,f103,f161])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(sK0)) | (~spl6_2 | ~spl6_5)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f105,f120,f84])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ~spl6_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f52,f133])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ((k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f40,f39,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f19])).
% 0.22/0.49  fof(f19,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    spl6_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f53,f128])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f41])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    spl6_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f54,f123])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f41])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    spl6_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f55,f118])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f41])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    spl6_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f56,f113])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    v2_tex_2(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl6_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f108])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f58,f103])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    r2_hidden(sK2,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ~spl6_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f59,f98])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (4192)------------------------------
% 0.22/0.50  % (4192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4192)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (4192)Memory used [KB]: 7803
% 0.22/0.50  % (4192)Time elapsed: 0.074 s
% 0.22/0.50  % (4192)------------------------------
% 0.22/0.50  % (4192)------------------------------
% 0.22/0.50  % (4185)Success in time 0.131 s
%------------------------------------------------------------------------------
