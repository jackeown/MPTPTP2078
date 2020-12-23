%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  96 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  160 ( 289 expanded)
%              Number of equality atoms :   26 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f84,f86])).

fof(f86,plain,(
    ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl2_6 ),
    inference(resolution,[],[f83,f77])).

fof(f77,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(superposition,[],[f74,f76])).

fof(f76,plain,(
    ! [X0] : k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(forward_demodulation,[],[f75,f32])).

fof(f32,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f75,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f63,f31])).

fof(f31,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f36,f34])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f74,plain,(
    ! [X0] : ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0) ),
    inference(forward_demodulation,[],[f73,f32])).

fof(f73,plain,(
    ! [X0] : ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
    inference(resolution,[],[f62,f31])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f35,f34])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f83,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_6
  <=> v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f84,plain,
    ( ~ spl2_4
    | ~ spl2_3
    | spl2_6
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f79,f49,f45,f82,f53,f57])).

fof(f57,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f53,plain,
    ( spl2_3
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f45,plain,
    ( spl2_1
  <=> v1_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f49,plain,
    ( spl2_2
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f79,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f78,f50])).

fof(f50,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f78,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f60,f46])).

fof(f46,plain,
    ( v1_tex_2(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f39,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_subset_1(X2,u1_struct_0(X0))
                  | ~ v1_tex_2(X1,X0) )
                & ( v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f59,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( v1_tex_2(sK1,sK0)
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24,f23])).

% (23737)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (23748)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_tex_2(X1,X0)
            & u1_struct_0(X0) = u1_struct_0(X1)
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( v1_tex_2(X1,sK0)
          & u1_struct_0(X1) = u1_struct_0(sK0)
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( v1_tex_2(X1,sK0)
        & u1_struct_0(X1) = u1_struct_0(sK0)
        & m1_pre_topc(X1,sK0) )
   => ( v1_tex_2(sK1,sK0)
      & u1_struct_0(sK0) = u1_struct_0(sK1)
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ~ ( v1_tex_2(X1,X0)
                & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

fof(f55,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

% (23737)Refutation not found, incomplete strategy% (23737)------------------------------
% (23737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23737)Termination reason: Refutation not found, incomplete strategy

% (23737)Memory used [KB]: 10618
% (23737)Time elapsed: 0.060 s
% (23737)------------------------------
% (23737)------------------------------
fof(f51,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f29,f49])).

fof(f29,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f30,f45])).

fof(f30,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:43:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (23740)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (23740)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f84,f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ~spl2_6),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    $false | ~spl2_6),
% 0.21/0.47    inference(resolution,[],[f83,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.21/0.47    inference(superposition,[],[f74,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0] : (k2_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.47    inference(forward_demodulation,[],[f75,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(resolution,[],[f63,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_orders_2(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.47    inference(resolution,[],[f36,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f73,f32])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0)))) )),
% 0.21/0.47    inference(resolution,[],[f62,f31])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_orders_2(X0) | ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))) )),
% 0.21/0.47    inference(resolution,[],[f35,f34])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_struct_0(X0) | ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl2_6 <=> v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ~spl2_4 | ~spl2_3 | spl2_6 | ~spl2_1 | ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f79,f49,f45,f82,f53,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl2_4 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl2_3 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl2_1 <=> v1_tex_2(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl2_2 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_2)),
% 0.21/0.47    inference(forward_demodulation,[],[f78,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.21/0.47    inference(resolution,[],[f60,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v1_tex_2(sK1,sK0) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f45])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(global_subsumption,[],[f39,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) & (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f57])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    (v1_tex_2(sK1,sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24,f23])).
% 0.21/0.47  % (23737)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (23748)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (v1_tex_2(X1,sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X1] : (v1_tex_2(X1,sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & m1_pre_topc(X1,sK0)) => (v1_tex_2(sK1,sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & m1_pre_topc(sK1,sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f53])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    m1_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  % (23737)Refutation not found, incomplete strategy% (23737)------------------------------
% 0.21/0.48  % (23737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23737)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (23737)Memory used [KB]: 10618
% 0.21/0.48  % (23737)Time elapsed: 0.060 s
% 0.21/0.48  % (23737)------------------------------
% 0.21/0.48  % (23737)------------------------------
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f49])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f45])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v1_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (23740)------------------------------
% 0.21/0.48  % (23740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23740)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (23740)Memory used [KB]: 10618
% 0.21/0.48  % (23740)Time elapsed: 0.054 s
% 0.21/0.48  % (23740)------------------------------
% 0.21/0.48  % (23740)------------------------------
% 0.21/0.48  % (23732)Success in time 0.118 s
%------------------------------------------------------------------------------
