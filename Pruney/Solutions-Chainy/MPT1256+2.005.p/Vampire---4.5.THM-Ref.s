%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 150 expanded)
%              Number of leaves         :   25 (  72 expanded)
%              Depth                    :    6
%              Number of atoms          :  215 ( 370 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f56,f63,f69,f101,f136,f149,f155,f218,f301,f314,f315])).

fof(f315,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) != k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f314,plain,
    ( spl2_44
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f309,f60,f53,f47,f311])).

fof(f311,plain,
    ( spl2_44
  <=> k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f47,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f53,plain,
    ( spl2_4
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f60,plain,
    ( spl2_5
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f309,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f243,f62])).

fof(f62,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f243,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f49,f55,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f55,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f49,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f301,plain,
    ( spl2_42
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f296,f133,f53,f47,f298])).

fof(f298,plain,
    ( spl2_42
  <=> r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f133,plain,
    ( spl2_17
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f296,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f246,f135])).

fof(f135,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f246,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f49,f55,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tops_1)).

fof(f218,plain,
    ( spl2_30
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f157,f152,f47,f215])).

fof(f215,plain,
    ( spl2_30
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f152,plain,
    ( spl2_20
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f157,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f49,f154,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f154,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f152])).

fof(f155,plain,
    ( spl2_20
    | ~ spl2_11
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f150,f146,f98,f152])).

fof(f98,plain,
    ( spl2_11
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f146,plain,
    ( spl2_19
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f150,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11
    | ~ spl2_19 ),
    inference(backward_demodulation,[],[f100,f148])).

fof(f148,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f146])).

fof(f100,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f98])).

fof(f149,plain,
    ( spl2_19
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f137,f47,f42,f146])).

fof(f42,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f137,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f49,f44,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f44,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f136,plain,
    ( spl2_17
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f124,f47,f42,f133])).

fof(f124,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f49,f44,f31])).

fof(f101,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f90,f66,f42,f98])).

fof(f66,plain,
    ( spl2_6
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f90,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f44,f68,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f68,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f69,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f64,f47,f42,f66])).

fof(f64,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f49,f44,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f63,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f57,f42,f60])).

fof(f57,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f44,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

% (15052)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f56,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f51,f42,f53])).

fof(f51,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f44,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f50,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f25,f47])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

fof(f45,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f42])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f27,f37])).

fof(f37,plain,
    ( spl2_1
  <=> r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f27,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:13:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (15049)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.52  % (15048)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (15065)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (15046)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.53  % (15044)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.53  % (15045)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.53  % (15047)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.53  % (15047)Refutation not found, incomplete strategy% (15047)------------------------------
% 0.21/0.53  % (15047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15057)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.53  % (15050)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.54  % (15050)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (15047)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15047)Memory used [KB]: 10490
% 0.21/0.54  % (15047)Time elapsed: 0.097 s
% 0.21/0.54  % (15047)------------------------------
% 0.21/0.54  % (15047)------------------------------
% 0.21/0.55  % (15067)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.55  % (15066)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.55  % (15067)Refutation not found, incomplete strategy% (15067)------------------------------
% 0.21/0.55  % (15067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15067)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15067)Memory used [KB]: 10618
% 0.21/0.55  % (15067)Time elapsed: 0.058 s
% 0.21/0.55  % (15067)------------------------------
% 0.21/0.55  % (15067)------------------------------
% 0.21/0.55  % (15064)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.55  % (15063)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.55  % (15062)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.55  % (15055)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.55  % (15059)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.55  % (15053)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.55  % (15058)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.56  % (15056)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f316,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f40,f45,f50,f56,f63,f69,f101,f136,f149,f155,f218,f301,f314,f315])).
% 0.21/0.56  fof(f315,plain,(
% 0.21/0.56    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) != k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1))),
% 0.21/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  fof(f314,plain,(
% 0.21/0.56    spl2_44 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f309,f60,f53,f47,f311])).
% 0.21/0.56  fof(f311,plain,(
% 0.21/0.56    spl2_44 <=> k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    spl2_3 <=> l1_pre_topc(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    spl2_4 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    spl2_5 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.56  fof(f309,plain,(
% 0.21/0.56    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.21/0.56    inference(forward_demodulation,[],[f243,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f60])).
% 0.21/0.56  fof(f243,plain,(
% 0.21/0.56    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_3 | ~spl2_4)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f49,f55,f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f53])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    l1_pre_topc(sK0) | ~spl2_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f47])).
% 0.21/0.56  fof(f301,plain,(
% 0.21/0.56    spl2_42 | ~spl2_3 | ~spl2_4 | ~spl2_17),
% 0.21/0.56    inference(avatar_split_clause,[],[f296,f133,f53,f47,f298])).
% 0.21/0.56  fof(f298,plain,(
% 0.21/0.56    spl2_42 <=> r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.21/0.56  fof(f133,plain,(
% 0.21/0.56    spl2_17 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.56  fof(f296,plain,(
% 0.21/0.56    r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_17)),
% 0.21/0.56    inference(forward_demodulation,[],[f246,f135])).
% 0.21/0.56  fof(f135,plain,(
% 0.21/0.56    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_17),
% 0.21/0.56    inference(avatar_component_clause,[],[f133])).
% 0.21/0.56  fof(f246,plain,(
% 0.21/0.56    r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_3 | ~spl2_4)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f49,f55,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tops_1)).
% 0.21/0.56  fof(f218,plain,(
% 0.21/0.56    spl2_30 | ~spl2_3 | ~spl2_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f157,f152,f47,f215])).
% 0.21/0.56  fof(f215,plain,(
% 0.21/0.56    spl2_30 <=> k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.56  fof(f152,plain,(
% 0.21/0.56    spl2_20 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.56  fof(f157,plain,(
% 0.21/0.56    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | (~spl2_3 | ~spl2_20)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f49,f154,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 0.21/0.56  fof(f154,plain,(
% 0.21/0.56    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_20),
% 0.21/0.56    inference(avatar_component_clause,[],[f152])).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    spl2_20 | ~spl2_11 | ~spl2_19),
% 0.21/0.56    inference(avatar_split_clause,[],[f150,f146,f98,f152])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    spl2_11 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.56  fof(f146,plain,(
% 0.21/0.56    spl2_19 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_11 | ~spl2_19)),
% 0.21/0.56    inference(backward_demodulation,[],[f100,f148])).
% 0.21/0.56  fof(f148,plain,(
% 0.21/0.56    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_19),
% 0.21/0.56    inference(avatar_component_clause,[],[f146])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_11),
% 0.21/0.56    inference(avatar_component_clause,[],[f98])).
% 0.21/0.56  fof(f149,plain,(
% 0.21/0.56    spl2_19 | ~spl2_2 | ~spl2_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f137,f47,f42,f146])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.56  fof(f137,plain,(
% 0.21/0.56    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f49,f44,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f42])).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    spl2_17 | ~spl2_2 | ~spl2_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f124,f47,f42,f133])).
% 0.21/0.56  fof(f124,plain,(
% 0.21/0.56    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_3)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f49,f44,f31])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    spl2_11 | ~spl2_2 | ~spl2_6),
% 0.21/0.56    inference(avatar_split_clause,[],[f90,f66,f42,f98])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    spl2_6 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_6)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f44,f68,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(flattening,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f66])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    spl2_6 | ~spl2_2 | ~spl2_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f64,f47,f42,f66])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f49,f44,f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    spl2_5 | ~spl2_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f57,f42,f60])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_2),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f44,f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  % (15052)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    spl2_4 | ~spl2_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f51,f42,f53])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f44,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    spl2_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f25,f47])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    l1_pre_topc(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f23,f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ? [X1] : (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,negated_conjecture,(
% 0.21/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 0.21/0.56    inference(negated_conjecture,[],[f9])).
% 0.21/0.56  fof(f9,conjecture,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    spl2_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f26,f42])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ~spl2_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f27,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    spl2_1 <=> r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (15050)------------------------------
% 0.21/0.56  % (15050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15050)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (15050)Memory used [KB]: 10874
% 0.21/0.56  % (15050)Time elapsed: 0.109 s
% 0.21/0.56  % (15050)------------------------------
% 0.21/0.56  % (15050)------------------------------
% 0.21/0.56  % (15054)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.56  % (15043)Success in time 0.192 s
%------------------------------------------------------------------------------
