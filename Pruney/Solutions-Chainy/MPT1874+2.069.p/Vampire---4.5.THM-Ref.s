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
% DateTime   : Thu Dec  3 13:21:31 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 127 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   16
%              Number of atoms          :  181 ( 597 expanded)
%              Number of equality atoms :   26 (  75 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f148,f151,f240])).

fof(f240,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f238])).

fof(f238,plain,
    ( k1_tarski(sK2) != k1_tarski(sK2)
    | ~ spl4_5 ),
    inference(superposition,[],[f74,f235])).

% (30459)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
fof(f235,plain,(
    k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(global_subsumption,[],[f20,f234])).

fof(f234,plain,
    ( ~ r2_hidden(sK2,sK1)
    | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(resolution,[],[f225,f19])).

fof(f19,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

fof(f225,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0))) ) ),
    inference(global_subsumption,[],[f68,f224])).

fof(f224,plain,(
    ! [X0] :
      ( k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0)))
      | ~ r2_hidden(X0,sK1)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f216,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f216,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0)))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f97,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f31,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f97,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK1)
      | k1_tarski(X1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X1)))
      | ~ r2_hidden(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f90,f31])).

fof(f90,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X6,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X6)) = X6 ) ),
    inference(global_subsumption,[],[f24,f25,f26,f23,f81])).

fof(f81,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X6,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X6)) = X6
      | ~ v2_tex_2(sK1,sK0) ) ),
    inference(resolution,[],[f27,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f23,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f43,f22])).

fof(f43,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f36,f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f20,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f74,plain,
    ( k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f21,f65])).

fof(f65,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_5
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f21,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f151,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl4_2 ),
    inference(resolution,[],[f50,f20])).

fof(f50,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_2
  <=> ! [X6] : ~ r2_hidden(X6,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f148,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f91,f49,f46])).

fof(f46,plain,
    ( spl4_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f40,f37])).

fof(f37,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f35,f22])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f36,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,
    ( spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f55,f46,f64])).

fof(f55,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    inference(resolution,[],[f33,f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:20:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (1217822720)
% 0.14/0.37  ipcrm: permission denied for id (1224409089)
% 0.14/0.37  ipcrm: permission denied for id (1217888258)
% 0.14/0.37  ipcrm: permission denied for id (1222082564)
% 0.14/0.37  ipcrm: permission denied for id (1222115333)
% 0.14/0.38  ipcrm: permission denied for id (1217986566)
% 0.14/0.38  ipcrm: permission denied for id (1218019335)
% 0.14/0.38  ipcrm: permission denied for id (1226211336)
% 0.14/0.38  ipcrm: permission denied for id (1224507401)
% 0.14/0.38  ipcrm: permission denied for id (1224540170)
% 0.14/0.38  ipcrm: permission denied for id (1222246411)
% 0.14/0.38  ipcrm: permission denied for id (1222279180)
% 0.21/0.38  ipcrm: permission denied for id (1218150413)
% 0.21/0.39  ipcrm: permission denied for id (1218183182)
% 0.21/0.39  ipcrm: permission denied for id (1222311951)
% 0.21/0.39  ipcrm: permission denied for id (1218248720)
% 0.21/0.39  ipcrm: permission denied for id (1218281489)
% 0.21/0.39  ipcrm: permission denied for id (1222344722)
% 0.21/0.39  ipcrm: permission denied for id (1218347027)
% 0.21/0.39  ipcrm: permission denied for id (1222377492)
% 0.21/0.40  ipcrm: permission denied for id (1224572949)
% 0.21/0.40  ipcrm: permission denied for id (1218445334)
% 0.21/0.40  ipcrm: permission denied for id (1218478103)
% 0.21/0.40  ipcrm: permission denied for id (1218510872)
% 0.21/0.40  ipcrm: permission denied for id (1222443033)
% 0.21/0.40  ipcrm: permission denied for id (1218576410)
% 0.21/0.40  ipcrm: permission denied for id (1218609179)
% 0.21/0.40  ipcrm: permission denied for id (1218641948)
% 0.21/0.41  ipcrm: permission denied for id (1218674717)
% 0.21/0.41  ipcrm: permission denied for id (1225687070)
% 0.21/0.41  ipcrm: permission denied for id (1224638495)
% 0.21/0.41  ipcrm: permission denied for id (1222541344)
% 0.21/0.41  ipcrm: permission denied for id (1225719841)
% 0.21/0.41  ipcrm: permission denied for id (1222606882)
% 0.21/0.41  ipcrm: permission denied for id (1218871331)
% 0.21/0.41  ipcrm: permission denied for id (1222639652)
% 0.21/0.42  ipcrm: permission denied for id (1226244133)
% 0.21/0.42  ipcrm: permission denied for id (1218969638)
% 0.21/0.42  ipcrm: permission denied for id (1222705191)
% 0.21/0.42  ipcrm: permission denied for id (1219067944)
% 0.21/0.42  ipcrm: permission denied for id (1219100713)
% 0.21/0.42  ipcrm: permission denied for id (1222737962)
% 0.21/0.42  ipcrm: permission denied for id (1225785387)
% 0.21/0.42  ipcrm: permission denied for id (1219231788)
% 0.21/0.43  ipcrm: permission denied for id (1219264557)
% 0.21/0.43  ipcrm: permission denied for id (1224769582)
% 0.21/0.43  ipcrm: permission denied for id (1224802351)
% 0.21/0.43  ipcrm: permission denied for id (1224835120)
% 0.21/0.43  ipcrm: permission denied for id (1219395633)
% 0.21/0.43  ipcrm: permission denied for id (1219428402)
% 0.21/0.43  ipcrm: permission denied for id (1222934579)
% 0.21/0.43  ipcrm: permission denied for id (1222967348)
% 0.21/0.44  ipcrm: permission denied for id (1223000117)
% 0.21/0.44  ipcrm: permission denied for id (1224867894)
% 0.21/0.44  ipcrm: permission denied for id (1223065655)
% 0.21/0.44  ipcrm: permission denied for id (1223098424)
% 0.21/0.44  ipcrm: permission denied for id (1223131193)
% 0.21/0.44  ipcrm: permission denied for id (1219690554)
% 0.21/0.44  ipcrm: permission denied for id (1219723323)
% 0.21/0.44  ipcrm: permission denied for id (1219756092)
% 0.21/0.45  ipcrm: permission denied for id (1223163965)
% 0.21/0.45  ipcrm: permission denied for id (1226473534)
% 0.21/0.45  ipcrm: permission denied for id (1225850943)
% 0.21/0.45  ipcrm: permission denied for id (1219887168)
% 0.21/0.45  ipcrm: permission denied for id (1219952705)
% 0.21/0.45  ipcrm: permission denied for id (1223262274)
% 0.21/0.45  ipcrm: permission denied for id (1223295043)
% 0.21/0.45  ipcrm: permission denied for id (1220051012)
% 0.21/0.46  ipcrm: permission denied for id (1224966213)
% 0.21/0.46  ipcrm: permission denied for id (1220116550)
% 0.21/0.46  ipcrm: permission denied for id (1225883719)
% 0.21/0.46  ipcrm: permission denied for id (1220182088)
% 0.21/0.46  ipcrm: permission denied for id (1220214857)
% 0.21/0.46  ipcrm: permission denied for id (1225916490)
% 0.21/0.46  ipcrm: permission denied for id (1225064523)
% 0.21/0.46  ipcrm: permission denied for id (1220313164)
% 0.21/0.47  ipcrm: permission denied for id (1225097293)
% 0.21/0.47  ipcrm: permission denied for id (1223491662)
% 0.21/0.47  ipcrm: permission denied for id (1220411471)
% 0.21/0.47  ipcrm: permission denied for id (1223524432)
% 0.21/0.47  ipcrm: permission denied for id (1225130065)
% 0.21/0.47  ipcrm: permission denied for id (1220509778)
% 0.21/0.47  ipcrm: permission denied for id (1220542547)
% 0.21/0.47  ipcrm: permission denied for id (1223589972)
% 0.21/0.48  ipcrm: permission denied for id (1220608085)
% 0.21/0.48  ipcrm: permission denied for id (1220640854)
% 0.21/0.48  ipcrm: permission denied for id (1223622743)
% 0.21/0.48  ipcrm: permission denied for id (1226506328)
% 0.21/0.48  ipcrm: permission denied for id (1225982041)
% 0.21/0.48  ipcrm: permission denied for id (1220771930)
% 0.21/0.48  ipcrm: permission denied for id (1220804699)
% 0.21/0.48  ipcrm: permission denied for id (1220837468)
% 0.21/0.49  ipcrm: permission denied for id (1225228381)
% 0.21/0.49  ipcrm: permission denied for id (1220903006)
% 0.21/0.49  ipcrm: permission denied for id (1223753823)
% 0.21/0.49  ipcrm: permission denied for id (1220968544)
% 0.21/0.49  ipcrm: permission denied for id (1221001313)
% 0.21/0.49  ipcrm: permission denied for id (1226014818)
% 0.21/0.49  ipcrm: permission denied for id (1221066851)
% 0.21/0.50  ipcrm: permission denied for id (1225326693)
% 0.21/0.50  ipcrm: permission denied for id (1221165158)
% 0.21/0.50  ipcrm: permission denied for id (1221197927)
% 0.21/0.50  ipcrm: permission denied for id (1221230696)
% 0.21/0.50  ipcrm: permission denied for id (1221263465)
% 0.21/0.50  ipcrm: permission denied for id (1223884906)
% 0.21/0.50  ipcrm: permission denied for id (1225359467)
% 0.21/0.50  ipcrm: permission denied for id (1221361772)
% 0.21/0.51  ipcrm: permission denied for id (1221394541)
% 0.21/0.51  ipcrm: permission denied for id (1223950446)
% 0.21/0.51  ipcrm: permission denied for id (1223983215)
% 0.21/0.51  ipcrm: permission denied for id (1225392240)
% 0.21/0.51  ipcrm: permission denied for id (1221492849)
% 0.21/0.51  ipcrm: permission denied for id (1226375282)
% 0.21/0.51  ipcrm: permission denied for id (1226571891)
% 0.21/0.51  ipcrm: permission denied for id (1221591156)
% 0.21/0.52  ipcrm: permission denied for id (1221623925)
% 0.21/0.52  ipcrm: permission denied for id (1224114294)
% 0.21/0.52  ipcrm: permission denied for id (1225490551)
% 0.21/0.52  ipcrm: permission denied for id (1221722232)
% 0.21/0.52  ipcrm: permission denied for id (1224212601)
% 0.21/0.52  ipcrm: permission denied for id (1226145914)
% 0.21/0.52  ipcrm: permission denied for id (1225588859)
% 0.21/0.52  ipcrm: permission denied for id (1224310908)
% 0.36/0.53  ipcrm: permission denied for id (1224343677)
% 0.36/0.53  ipcrm: permission denied for id (1224376446)
% 0.36/0.53  ipcrm: permission denied for id (1221984383)
% 0.38/0.64  % (30464)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.38/0.65  % (30456)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.38/0.65  % (30456)Refutation found. Thanks to Tanya!
% 0.38/0.65  % SZS status Theorem for theBenchmark
% 0.38/0.65  % SZS output start Proof for theBenchmark
% 0.38/0.65  fof(f241,plain,(
% 0.38/0.65    $false),
% 0.38/0.65    inference(avatar_sat_refutation,[],[f67,f148,f151,f240])).
% 0.38/0.65  fof(f240,plain,(
% 0.38/0.65    ~spl4_5),
% 0.38/0.65    inference(avatar_contradiction_clause,[],[f239])).
% 0.38/0.65  fof(f239,plain,(
% 0.38/0.65    $false | ~spl4_5),
% 0.38/0.65    inference(trivial_inequality_removal,[],[f238])).
% 0.38/0.65  fof(f238,plain,(
% 0.38/0.65    k1_tarski(sK2) != k1_tarski(sK2) | ~spl4_5),
% 0.38/0.65    inference(superposition,[],[f74,f235])).
% 0.38/0.65  % (30459)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.38/0.66  fof(f235,plain,(
% 0.38/0.66    k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))),
% 0.38/0.66    inference(global_subsumption,[],[f20,f234])).
% 0.38/0.66  fof(f234,plain,(
% 0.38/0.66    ~r2_hidden(sK2,sK1) | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))),
% 0.38/0.66    inference(resolution,[],[f225,f19])).
% 0.38/0.66  fof(f19,plain,(
% 0.38/0.66    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.38/0.66    inference(cnf_transformation,[],[f10])).
% 0.38/0.66  fof(f10,plain,(
% 0.38/0.66    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.38/0.66    inference(flattening,[],[f9])).
% 0.38/0.66  fof(f9,plain,(
% 0.38/0.66    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.38/0.66    inference(ennf_transformation,[],[f8])).
% 0.38/0.66  fof(f8,negated_conjecture,(
% 0.38/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.38/0.66    inference(negated_conjecture,[],[f7])).
% 0.38/0.66  fof(f7,conjecture,(
% 0.38/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).
% 0.38/0.66  fof(f225,plain,(
% 0.38/0.66    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0)))) )),
% 0.38/0.66    inference(global_subsumption,[],[f68,f224])).
% 0.38/0.66  fof(f224,plain,(
% 0.38/0.66    ( ! [X0] : (k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0))) | ~r2_hidden(X0,sK1) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.38/0.66    inference(resolution,[],[f216,f32])).
% 0.38/0.66  fof(f32,plain,(
% 0.38/0.66    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f15])).
% 0.38/0.66  fof(f15,plain,(
% 0.38/0.66    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.38/0.66    inference(flattening,[],[f14])).
% 0.38/0.66  fof(f14,plain,(
% 0.38/0.66    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.38/0.66    inference(ennf_transformation,[],[f2])).
% 0.38/0.66  fof(f2,axiom,(
% 0.38/0.66    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.38/0.66  fof(f216,plain,(
% 0.38/0.66    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK0)) | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0))) | ~r2_hidden(X0,sK1)) )),
% 0.38/0.66    inference(resolution,[],[f97,f39])).
% 0.38/0.66  fof(f39,plain,(
% 0.38/0.66    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.38/0.66    inference(resolution,[],[f31,f35])).
% 0.38/0.66  fof(f35,plain,(
% 0.38/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f3])).
% 0.38/0.66  fof(f3,axiom,(
% 0.38/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.38/0.66  fof(f31,plain,(
% 0.38/0.66    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f13])).
% 0.38/0.66  fof(f13,plain,(
% 0.38/0.66    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.38/0.66    inference(ennf_transformation,[],[f1])).
% 0.38/0.66  fof(f1,axiom,(
% 0.38/0.66    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.38/0.66  fof(f97,plain,(
% 0.38/0.66    ( ! [X1] : (~r1_tarski(k1_tarski(X1),sK1) | k1_tarski(X1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X1))) | ~r2_hidden(X1,u1_struct_0(sK0))) )),
% 0.38/0.66    inference(resolution,[],[f90,f31])).
% 0.38/0.66  fof(f90,plain,(
% 0.38/0.66    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X6,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X6)) = X6) )),
% 0.38/0.66    inference(global_subsumption,[],[f24,f25,f26,f23,f81])).
% 0.38/0.66  fof(f81,plain,(
% 0.38/0.66    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X6,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X6)) = X6 | ~v2_tex_2(sK1,sK0)) )),
% 0.38/0.66    inference(resolution,[],[f27,f22])).
% 0.38/0.66  fof(f22,plain,(
% 0.38/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.38/0.66    inference(cnf_transformation,[],[f10])).
% 0.38/0.66  fof(f27,plain,(
% 0.38/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~v2_tex_2(X1,X0)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f12])).
% 0.38/0.66  fof(f12,plain,(
% 0.38/0.66    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.38/0.66    inference(flattening,[],[f11])).
% 0.38/0.66  fof(f11,plain,(
% 0.38/0.66    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.38/0.66    inference(ennf_transformation,[],[f6])).
% 0.38/0.66  fof(f6,axiom,(
% 0.38/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 0.38/0.66  fof(f23,plain,(
% 0.38/0.66    v2_tex_2(sK1,sK0)),
% 0.38/0.66    inference(cnf_transformation,[],[f10])).
% 0.38/0.66  fof(f26,plain,(
% 0.38/0.66    l1_pre_topc(sK0)),
% 0.38/0.66    inference(cnf_transformation,[],[f10])).
% 0.38/0.66  fof(f25,plain,(
% 0.38/0.66    v2_pre_topc(sK0)),
% 0.38/0.66    inference(cnf_transformation,[],[f10])).
% 0.38/0.66  fof(f24,plain,(
% 0.38/0.66    ~v2_struct_0(sK0)),
% 0.38/0.66    inference(cnf_transformation,[],[f10])).
% 0.38/0.66  fof(f68,plain,(
% 0.38/0.66    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.38/0.66    inference(resolution,[],[f43,f22])).
% 0.38/0.66  fof(f43,plain,(
% 0.38/0.66    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.38/0.66    inference(resolution,[],[f36,f20])).
% 0.38/0.66  fof(f36,plain,(
% 0.38/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f18])).
% 0.38/0.66  fof(f18,plain,(
% 0.38/0.66    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.38/0.66    inference(ennf_transformation,[],[f4])).
% 0.38/0.66  fof(f4,axiom,(
% 0.38/0.66    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.38/0.66  fof(f20,plain,(
% 0.38/0.66    r2_hidden(sK2,sK1)),
% 0.38/0.66    inference(cnf_transformation,[],[f10])).
% 0.38/0.66  fof(f74,plain,(
% 0.38/0.66    k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | ~spl4_5),
% 0.38/0.66    inference(backward_demodulation,[],[f21,f65])).
% 0.38/0.66  fof(f65,plain,(
% 0.38/0.66    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | ~spl4_5),
% 0.38/0.66    inference(avatar_component_clause,[],[f64])).
% 0.38/0.66  fof(f64,plain,(
% 0.38/0.66    spl4_5 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 0.38/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.38/0.66  fof(f21,plain,(
% 0.38/0.66    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.38/0.66    inference(cnf_transformation,[],[f10])).
% 0.38/0.66  fof(f151,plain,(
% 0.38/0.66    ~spl4_2),
% 0.38/0.66    inference(avatar_contradiction_clause,[],[f149])).
% 0.38/0.66  fof(f149,plain,(
% 0.38/0.66    $false | ~spl4_2),
% 0.38/0.66    inference(resolution,[],[f50,f20])).
% 0.38/0.66  fof(f50,plain,(
% 0.38/0.66    ( ! [X6] : (~r2_hidden(X6,sK1)) ) | ~spl4_2),
% 0.38/0.66    inference(avatar_component_clause,[],[f49])).
% 0.38/0.66  fof(f49,plain,(
% 0.38/0.66    spl4_2 <=> ! [X6] : ~r2_hidden(X6,sK1)),
% 0.38/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.38/0.66  fof(f148,plain,(
% 0.38/0.66    ~spl4_1 | spl4_2),
% 0.38/0.66    inference(avatar_split_clause,[],[f91,f49,f46])).
% 0.38/0.66  fof(f46,plain,(
% 0.38/0.66    spl4_1 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.38/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.38/0.66  fof(f91,plain,(
% 0.38/0.66    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(u1_struct_0(sK0))) )),
% 0.38/0.66    inference(resolution,[],[f40,f37])).
% 0.38/0.66  fof(f37,plain,(
% 0.38/0.66    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.38/0.66    inference(resolution,[],[f35,f22])).
% 0.38/0.66  fof(f40,plain,(
% 0.38/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.38/0.66    inference(resolution,[],[f36,f34])).
% 0.38/0.66  fof(f34,plain,(
% 0.38/0.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f3])).
% 0.38/0.66  fof(f67,plain,(
% 0.38/0.66    spl4_5 | spl4_1),
% 0.38/0.66    inference(avatar_split_clause,[],[f55,f46,f64])).
% 0.38/0.66  fof(f55,plain,(
% 0.38/0.66    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 0.38/0.66    inference(resolution,[],[f33,f19])).
% 0.38/0.66  fof(f33,plain,(
% 0.38/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f17])).
% 0.38/0.66  fof(f17,plain,(
% 0.38/0.66    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.38/0.66    inference(flattening,[],[f16])).
% 0.38/0.66  fof(f16,plain,(
% 0.38/0.66    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.38/0.66    inference(ennf_transformation,[],[f5])).
% 0.38/0.66  fof(f5,axiom,(
% 0.38/0.66    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.38/0.66  % SZS output end Proof for theBenchmark
% 0.38/0.66  % (30456)------------------------------
% 0.38/0.66  % (30456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (30456)Termination reason: Refutation
% 0.38/0.66  
% 0.38/0.66  % (30456)Memory used [KB]: 10874
% 0.38/0.66  % (30456)Time elapsed: 0.086 s
% 0.38/0.66  % (30456)------------------------------
% 0.38/0.66  % (30456)------------------------------
% 0.38/0.66  % (30286)Success in time 0.297 s
%------------------------------------------------------------------------------
