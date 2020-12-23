%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:08 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 355 expanded)
%              Number of leaves         :   11 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  201 (1611 expanded)
%              Number of equality atoms :    8 (  32 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f117,f141,f162])).

% (8575)Refutation not found, incomplete strategy% (8575)------------------------------
% (8575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f162,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f155])).

% (8575)Termination reason: Refutation not found, incomplete strategy

% (8575)Memory used [KB]: 6396
% (8575)Time elapsed: 0.121 s
% (8575)------------------------------
% (8575)------------------------------
fof(f155,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f42,f41,f38,f88,f78,f147,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f147,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f142,f142,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f142,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f41,f42,f40,f39,f38,f85,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f85,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_1
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f77,f76])).

fof(f76,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f74,f39,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f74,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f40,f73,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f73,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f42,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f77,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f74,f39,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f88,plain,
    ( ~ m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_2
  <=> m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f141,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f42,f41,f38,f89,f78,f122,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f122,plain,
    ( ! [X0] : ~ r1_tarski(k2_tarski(sK1,X0),k1_tops_1(sK0,sK2))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f118,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f118,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f41,f42,f40,f39,f38,f84,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f89,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f117,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f80,f87,f83])).

fof(f80,plain,
    ( ~ m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f37,f76])).

fof(f37,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f79,f87,f83])).

fof(f79,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f36,f76])).

fof(f36,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:10:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (8555)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (8563)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (8566)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (8561)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (8574)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.52  % (8561)Refutation not found, incomplete strategy% (8561)------------------------------
% 0.22/0.52  % (8561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8561)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8561)Memory used [KB]: 10618
% 0.22/0.52  % (8561)Time elapsed: 0.118 s
% 0.22/0.52  % (8561)------------------------------
% 0.22/0.52  % (8561)------------------------------
% 0.22/0.52  % (8558)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (8562)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (8549)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (8556)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.28/0.53  % (8553)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.28/0.53  % (8574)Refutation found. Thanks to Tanya!
% 1.28/0.53  % SZS status Theorem for theBenchmark
% 1.28/0.53  % (8575)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.28/0.53  % (8565)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f163,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(avatar_sat_refutation,[],[f90,f117,f141,f162])).
% 1.28/0.53  % (8575)Refutation not found, incomplete strategy% (8575)------------------------------
% 1.28/0.53  % (8575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  fof(f162,plain,(
% 1.28/0.53    ~spl3_1 | spl3_2),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f155])).
% 1.28/0.53  % (8575)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (8575)Memory used [KB]: 6396
% 1.28/0.53  % (8575)Time elapsed: 0.121 s
% 1.28/0.53  % (8575)------------------------------
% 1.28/0.53  % (8575)------------------------------
% 1.28/0.53  fof(f155,plain,(
% 1.28/0.53    $false | (~spl3_1 | spl3_2)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f42,f41,f38,f88,f78,f147,f47])).
% 1.28/0.53  fof(f47,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f26])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.28/0.53    inference(flattening,[],[f25])).
% 1.28/0.53  fof(f25,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.28/0.53    inference(ennf_transformation,[],[f12])).
% 1.28/0.53  fof(f12,axiom,(
% 1.28/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
% 1.28/0.53  fof(f147,plain,(
% 1.28/0.53    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | ~spl3_1),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f142,f142,f56])).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f5])).
% 1.28/0.53  fof(f5,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.28/0.53  fof(f142,plain,(
% 1.28/0.53    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl3_1),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f41,f42,f40,f39,f38,f85,f45])).
% 1.28/0.53  fof(f45,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f22])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.28/0.53    inference(flattening,[],[f21])).
% 1.28/0.53  fof(f21,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.28/0.53    inference(ennf_transformation,[],[f11])).
% 1.28/0.53  fof(f11,axiom,(
% 1.28/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 1.28/0.53  fof(f85,plain,(
% 1.28/0.53    m1_connsp_2(sK2,sK0,sK1) | ~spl3_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f83])).
% 1.28/0.53  fof(f83,plain,(
% 1.28/0.53    spl3_1 <=> m1_connsp_2(sK2,sK0,sK1)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.28/0.53  fof(f39,plain,(
% 1.28/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.28/0.53    inference(flattening,[],[f17])).
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.28/0.53    inference(ennf_transformation,[],[f16])).
% 1.28/0.53  fof(f16,negated_conjecture,(
% 1.28/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.28/0.53    inference(negated_conjecture,[],[f15])).
% 1.28/0.53  fof(f15,conjecture,(
% 1.28/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).
% 1.28/0.53  fof(f40,plain,(
% 1.28/0.53    ~v2_struct_0(sK0)),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f78,plain,(
% 1.28/0.53    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.28/0.53    inference(backward_demodulation,[],[f77,f76])).
% 1.28/0.53  fof(f76,plain,(
% 1.28/0.53    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f74,f39,f63])).
% 1.28/0.53  fof(f63,plain,(
% 1.28/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f50,f61])).
% 1.28/0.53  fof(f61,plain,(
% 1.28/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f3])).
% 1.28/0.53  fof(f3,axiom,(
% 1.28/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.28/0.53  fof(f50,plain,(
% 1.28/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f30])).
% 1.28/0.53  fof(f30,plain,(
% 1.28/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.28/0.53    inference(flattening,[],[f29])).
% 1.28/0.53  fof(f29,plain,(
% 1.28/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.28/0.53    inference(ennf_transformation,[],[f10])).
% 1.28/0.53  fof(f10,axiom,(
% 1.28/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.28/0.53  fof(f74,plain,(
% 1.28/0.53    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f40,f73,f53])).
% 1.28/0.53  fof(f53,plain,(
% 1.28/0.53    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f32])).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.28/0.53    inference(flattening,[],[f31])).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.28/0.53    inference(ennf_transformation,[],[f8])).
% 1.28/0.53  fof(f8,axiom,(
% 1.28/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.28/0.53  fof(f73,plain,(
% 1.28/0.53    l1_struct_0(sK0)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f42,f62])).
% 1.28/0.53  fof(f62,plain,(
% 1.28/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f35])).
% 1.28/0.53  fof(f35,plain,(
% 1.28/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,axiom,(
% 1.28/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.28/0.53  fof(f77,plain,(
% 1.28/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f74,f39,f49])).
% 1.28/0.53  fof(f49,plain,(
% 1.28/0.53    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.28/0.53    inference(flattening,[],[f27])).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.28/0.53    inference(ennf_transformation,[],[f9])).
% 1.28/0.53  fof(f9,axiom,(
% 1.28/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.28/0.53  fof(f88,plain,(
% 1.28/0.53    ~m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | spl3_2),
% 1.28/0.53    inference(avatar_component_clause,[],[f87])).
% 1.28/0.53  fof(f87,plain,(
% 1.28/0.53    spl3_2 <=> m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.28/0.53  fof(f38,plain,(
% 1.28/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f41,plain,(
% 1.28/0.53    v2_pre_topc(sK0)),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f42,plain,(
% 1.28/0.53    l1_pre_topc(sK0)),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f141,plain,(
% 1.28/0.53    spl3_1 | ~spl3_2),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f131])).
% 1.28/0.53  fof(f131,plain,(
% 1.28/0.53    $false | (spl3_1 | ~spl3_2)),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f42,f41,f38,f89,f78,f122,f48])).
% 1.28/0.53  fof(f48,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f26])).
% 1.28/0.53  fof(f122,plain,(
% 1.28/0.53    ( ! [X0] : (~r1_tarski(k2_tarski(sK1,X0),k1_tops_1(sK0,sK2))) ) | spl3_1),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f118,f54])).
% 1.28/0.53  fof(f54,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f5])).
% 1.28/0.53  fof(f118,plain,(
% 1.28/0.53    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl3_1),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f41,f42,f40,f39,f38,f84,f44])).
% 1.28/0.53  fof(f44,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f22])).
% 1.28/0.53  fof(f84,plain,(
% 1.28/0.53    ~m1_connsp_2(sK2,sK0,sK1) | spl3_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f83])).
% 1.28/0.53  fof(f89,plain,(
% 1.28/0.53    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | ~spl3_2),
% 1.28/0.53    inference(avatar_component_clause,[],[f87])).
% 1.28/0.53  fof(f117,plain,(
% 1.28/0.53    ~spl3_1 | ~spl3_2),
% 1.28/0.53    inference(avatar_split_clause,[],[f80,f87,f83])).
% 1.28/0.53  fof(f80,plain,(
% 1.28/0.53    ~m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | ~m1_connsp_2(sK2,sK0,sK1)),
% 1.28/0.53    inference(backward_demodulation,[],[f37,f76])).
% 1.28/0.53  fof(f37,plain,(
% 1.28/0.53    ~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f90,plain,(
% 1.28/0.53    spl3_1 | spl3_2),
% 1.28/0.53    inference(avatar_split_clause,[],[f79,f87,f83])).
% 1.28/0.53  fof(f79,plain,(
% 1.28/0.53    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | m1_connsp_2(sK2,sK0,sK1)),
% 1.28/0.53    inference(backward_demodulation,[],[f36,f76])).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (8574)------------------------------
% 1.28/0.53  % (8574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (8574)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (8574)Memory used [KB]: 6268
% 1.28/0.53  % (8574)Time elapsed: 0.120 s
% 1.28/0.53  % (8574)------------------------------
% 1.28/0.53  % (8574)------------------------------
% 1.28/0.53  % (8548)Success in time 0.17 s
%------------------------------------------------------------------------------
