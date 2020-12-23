%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:36 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 101 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  197 ( 338 expanded)
%              Number of equality atoms :   33 (  64 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f73,f75,f77])).

fof(f77,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | ~ spl4_6 ),
    inference(resolution,[],[f72,f55])).

fof(f55,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(superposition,[],[f27,f28])).

fof(f28,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f27,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f72,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_6
  <=> v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f75,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl4_5 ),
    inference(resolution,[],[f69,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f33,f57])).

fof(f57,plain,(
    ! [X0] : sK3(X0) = X0 ),
    inference(global_subsumption,[],[f34,f56])).

fof(f56,plain,(
    ! [X0] :
      ( sK3(X0) = X0
      | v1_subset_1(sK3(X0),X0) ) ),
    inference(resolution,[],[f36,f33])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f34,plain,(
    ! [X0] : ~ v1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK3(X0),X0)
      & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f33,plain,(
    ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_5
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f73,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | spl4_6
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f65,f52,f48,f44,f71,f68,f40])).

fof(f40,plain,
    ( spl4_1
  <=> v1_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f44,plain,
    ( spl4_2
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f48,plain,
    ( spl4_3
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f52,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f65,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tex_2(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f64,f45])).

fof(f45,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f64,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tex_2(sK1,sK0)
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f63,f45])).

fof(f63,plain,
    ( ~ v1_tex_2(sK1,sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f62,f49])).

fof(f49,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f62,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v1_tex_2(X0,sK0)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f37,f53])).

fof(f53,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

% (8222)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f54,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( v1_tex_2(sK1,sK0)
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14,f13])).

fof(f13,plain,
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

fof(f14,plain,
    ( ? [X1] :
        ( v1_tex_2(X1,sK0)
        & u1_struct_0(X1) = u1_struct_0(sK0)
        & m1_pre_topc(X1,sK0) )
   => ( v1_tex_2(sK1,sK0)
      & u1_struct_0(sK0) = u1_struct_0(sK1)
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ~ ( v1_tex_2(X1,X0)
                & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

fof(f50,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f48])).

fof(f24,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f44])).

fof(f25,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f26,f40])).

fof(f26,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n002.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:07:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.44  % (8233)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.44  % (8233)Refutation not found, incomplete strategy% (8233)------------------------------
% 0.18/0.44  % (8233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.44  % (8233)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.44  
% 0.18/0.44  % (8233)Memory used [KB]: 1663
% 0.18/0.44  % (8233)Time elapsed: 0.060 s
% 0.18/0.44  % (8233)------------------------------
% 0.18/0.44  % (8233)------------------------------
% 0.18/0.45  % (8235)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.18/0.45  % (8235)Refutation not found, incomplete strategy% (8235)------------------------------
% 0.18/0.45  % (8235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.45  % (8235)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.45  
% 0.18/0.45  % (8235)Memory used [KB]: 6140
% 0.18/0.45  % (8235)Time elapsed: 0.004 s
% 0.18/0.45  % (8235)------------------------------
% 0.18/0.45  % (8235)------------------------------
% 0.18/0.45  % (8227)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.18/0.45  % (8240)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.18/0.45  % (8240)Refutation not found, incomplete strategy% (8240)------------------------------
% 0.18/0.45  % (8240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.45  % (8240)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.45  
% 0.18/0.45  % (8240)Memory used [KB]: 10490
% 0.18/0.45  % (8240)Time elapsed: 0.062 s
% 0.18/0.45  % (8240)------------------------------
% 0.18/0.45  % (8240)------------------------------
% 0.18/0.45  % (8224)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.18/0.46  % (8224)Refutation not found, incomplete strategy% (8224)------------------------------
% 0.18/0.46  % (8224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (8224)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.46  
% 0.18/0.46  % (8224)Memory used [KB]: 1663
% 0.18/0.46  % (8224)Time elapsed: 0.063 s
% 0.18/0.46  % (8224)------------------------------
% 0.18/0.46  % (8224)------------------------------
% 0.18/0.46  % (8232)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.46  % (8232)Refutation not found, incomplete strategy% (8232)------------------------------
% 0.18/0.46  % (8232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (8232)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.46  
% 0.18/0.46  % (8232)Memory used [KB]: 6012
% 0.18/0.46  % (8232)Time elapsed: 0.003 s
% 0.18/0.46  % (8232)------------------------------
% 0.18/0.46  % (8232)------------------------------
% 0.18/0.47  % (8220)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.18/0.47  % (8226)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.47  % (8220)Refutation not found, incomplete strategy% (8220)------------------------------
% 0.18/0.47  % (8220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (8220)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.47  
% 0.18/0.47  % (8220)Memory used [KB]: 6140
% 0.18/0.47  % (8220)Time elapsed: 0.076 s
% 0.18/0.47  % (8220)------------------------------
% 0.18/0.47  % (8220)------------------------------
% 0.18/0.47  % (8226)Refutation found. Thanks to Tanya!
% 0.18/0.47  % SZS status Theorem for theBenchmark
% 0.18/0.47  % SZS output start Proof for theBenchmark
% 0.18/0.47  fof(f78,plain,(
% 0.18/0.47    $false),
% 0.18/0.47    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f73,f75,f77])).
% 0.18/0.47  fof(f77,plain,(
% 0.18/0.47    ~spl4_6),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f76])).
% 0.18/0.47  fof(f76,plain,(
% 0.18/0.47    $false | ~spl4_6),
% 0.18/0.47    inference(resolution,[],[f72,f55])).
% 0.18/0.47  fof(f55,plain,(
% 0.18/0.47    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.18/0.47    inference(superposition,[],[f27,f28])).
% 0.18/0.47  fof(f28,plain,(
% 0.18/0.47    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.18/0.47    inference(cnf_transformation,[],[f1])).
% 0.18/0.47  fof(f1,axiom,(
% 0.18/0.47    ! [X0] : k2_subset_1(X0) = X0),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.18/0.47  fof(f27,plain,(
% 0.18/0.47    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f2])).
% 0.18/0.47  fof(f2,axiom,(
% 0.18/0.47    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.18/0.47  fof(f72,plain,(
% 0.18/0.47    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl4_6),
% 0.18/0.47    inference(avatar_component_clause,[],[f71])).
% 0.18/0.47  fof(f71,plain,(
% 0.18/0.47    spl4_6 <=> v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.18/0.47  fof(f75,plain,(
% 0.18/0.47    spl4_5),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f74])).
% 0.18/0.47  fof(f74,plain,(
% 0.18/0.47    $false | spl4_5),
% 0.18/0.47    inference(resolution,[],[f69,f58])).
% 0.18/0.47  fof(f58,plain,(
% 0.18/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.18/0.47    inference(superposition,[],[f33,f57])).
% 0.18/0.47  fof(f57,plain,(
% 0.18/0.47    ( ! [X0] : (sK3(X0) = X0) )),
% 0.18/0.47    inference(global_subsumption,[],[f34,f56])).
% 0.18/0.47  fof(f56,plain,(
% 0.18/0.47    ( ! [X0] : (sK3(X0) = X0 | v1_subset_1(sK3(X0),X0)) )),
% 0.18/0.47    inference(resolution,[],[f36,f33])).
% 0.18/0.47  fof(f36,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f22])).
% 0.18/0.47  fof(f22,plain,(
% 0.18/0.47    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.47    inference(nnf_transformation,[],[f12])).
% 0.18/0.47  fof(f12,plain,(
% 0.18/0.47    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.47    inference(ennf_transformation,[],[f5])).
% 0.18/0.47  fof(f5,axiom,(
% 0.18/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.18/0.47  fof(f34,plain,(
% 0.18/0.47    ( ! [X0] : (~v1_subset_1(sK3(X0),X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f21])).
% 0.18/0.47  fof(f21,plain,(
% 0.18/0.47    ! [X0] : (~v1_subset_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)))),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3,f20])).
% 0.18/0.47  fof(f20,plain,(
% 0.18/0.47    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f3,axiom,(
% 0.18/0.47    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.18/0.47  fof(f33,plain,(
% 0.18/0.47    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(X0))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f21])).
% 0.18/0.47  fof(f69,plain,(
% 0.18/0.47    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_5),
% 0.18/0.47    inference(avatar_component_clause,[],[f68])).
% 0.18/0.47  fof(f68,plain,(
% 0.18/0.47    spl4_5 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.18/0.47  fof(f73,plain,(
% 0.18/0.47    ~spl4_1 | ~spl4_5 | spl4_6 | ~spl4_2 | ~spl4_3 | ~spl4_4),
% 0.18/0.47    inference(avatar_split_clause,[],[f65,f52,f48,f44,f71,f68,f40])).
% 0.18/0.47  fof(f40,plain,(
% 0.18/0.47    spl4_1 <=> v1_tex_2(sK1,sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.18/0.47  fof(f44,plain,(
% 0.18/0.47    spl4_2 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.18/0.47  fof(f48,plain,(
% 0.18/0.47    spl4_3 <=> m1_pre_topc(sK1,sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.18/0.47  fof(f52,plain,(
% 0.18/0.47    spl4_4 <=> l1_pre_topc(sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.18/0.47  fof(f65,plain,(
% 0.18/0.47    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tex_2(sK1,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.18/0.47    inference(forward_demodulation,[],[f64,f45])).
% 0.18/0.47  fof(f45,plain,(
% 0.18/0.47    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl4_2),
% 0.18/0.47    inference(avatar_component_clause,[],[f44])).
% 0.18/0.47  fof(f64,plain,(
% 0.18/0.47    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tex_2(sK1,sK0) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.18/0.47    inference(forward_demodulation,[],[f63,f45])).
% 0.18/0.47  fof(f63,plain,(
% 0.18/0.47    ~v1_tex_2(sK1,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | (~spl4_3 | ~spl4_4)),
% 0.18/0.47    inference(resolution,[],[f62,f49])).
% 0.18/0.47  fof(f49,plain,(
% 0.18/0.47    m1_pre_topc(sK1,sK0) | ~spl4_3),
% 0.18/0.47    inference(avatar_component_clause,[],[f48])).
% 0.18/0.47  fof(f62,plain,(
% 0.18/0.47    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v1_tex_2(X0,sK0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0))) ) | ~spl4_4),
% 0.18/0.47    inference(resolution,[],[f37,f53])).
% 0.18/0.47  fof(f53,plain,(
% 0.18/0.47    l1_pre_topc(sK0) | ~spl4_4),
% 0.18/0.47    inference(avatar_component_clause,[],[f52])).
% 0.18/0.47  fof(f37,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.18/0.47    inference(equality_resolution,[],[f29])).
% 0.18/0.47  fof(f29,plain,(
% 0.18/0.47    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f19])).
% 0.18/0.47  fof(f19,plain,(
% 0.18/0.47    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.18/0.47  fof(f18,plain,(
% 0.18/0.47    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f17,plain,(
% 0.18/0.47    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.18/0.47    inference(rectify,[],[f16])).
% 0.18/0.47  fof(f16,plain,(
% 0.18/0.47    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.18/0.47    inference(nnf_transformation,[],[f11])).
% 0.18/0.47  fof(f11,plain,(
% 0.18/0.47    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.18/0.47    inference(flattening,[],[f10])).
% 0.18/0.47  % (8222)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.18/0.47  fof(f10,plain,(
% 0.18/0.47    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f4])).
% 0.18/0.47  fof(f4,axiom,(
% 0.18/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.18/0.47  fof(f54,plain,(
% 0.18/0.47    spl4_4),
% 0.18/0.47    inference(avatar_split_clause,[],[f23,f52])).
% 0.18/0.47  fof(f23,plain,(
% 0.18/0.47    l1_pre_topc(sK0)),
% 0.18/0.47    inference(cnf_transformation,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    (v1_tex_2(sK1,sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14,f13])).
% 0.18/0.47  fof(f13,plain,(
% 0.18/0.47    ? [X0] : (? [X1] : (v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (v1_tex_2(X1,sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f14,plain,(
% 0.18/0.47    ? [X1] : (v1_tex_2(X1,sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & m1_pre_topc(X1,sK0)) => (v1_tex_2(sK1,sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & m1_pre_topc(sK1,sK0))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f9,plain,(
% 0.18/0.47    ? [X0] : (? [X1] : (v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.18/0.47    inference(flattening,[],[f8])).
% 0.18/0.47  fof(f8,plain,(
% 0.18/0.47    ? [X0] : (? [X1] : ((v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f7])).
% 0.18/0.47  fof(f7,negated_conjecture,(
% 0.18/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 0.18/0.47    inference(negated_conjecture,[],[f6])).
% 0.18/0.47  fof(f6,conjecture,(
% 0.18/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).
% 0.18/0.47  fof(f50,plain,(
% 0.18/0.47    spl4_3),
% 0.18/0.47    inference(avatar_split_clause,[],[f24,f48])).
% 0.18/0.47  fof(f24,plain,(
% 0.18/0.47    m1_pre_topc(sK1,sK0)),
% 0.18/0.47    inference(cnf_transformation,[],[f15])).
% 0.18/0.47  fof(f46,plain,(
% 0.18/0.47    spl4_2),
% 0.18/0.47    inference(avatar_split_clause,[],[f25,f44])).
% 0.18/0.47  fof(f25,plain,(
% 0.18/0.47    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.18/0.47    inference(cnf_transformation,[],[f15])).
% 0.18/0.47  fof(f42,plain,(
% 0.18/0.47    spl4_1),
% 0.18/0.47    inference(avatar_split_clause,[],[f26,f40])).
% 0.18/0.47  fof(f26,plain,(
% 0.18/0.47    v1_tex_2(sK1,sK0)),
% 0.18/0.47    inference(cnf_transformation,[],[f15])).
% 0.18/0.47  % SZS output end Proof for theBenchmark
% 0.18/0.47  % (8226)------------------------------
% 0.18/0.47  % (8226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (8226)Termination reason: Refutation
% 0.18/0.47  
% 0.18/0.47  % (8226)Memory used [KB]: 10618
% 0.18/0.47  % (8226)Time elapsed: 0.074 s
% 0.18/0.47  % (8226)------------------------------
% 0.18/0.47  % (8226)------------------------------
% 0.18/0.47  % (8230)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.18/0.47  % (8219)Success in time 0.126 s
%------------------------------------------------------------------------------
