%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:48 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 165 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  214 ( 601 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f215,f218,f237])).

fof(f237,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f38,f221])).

fof(f221,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(superposition,[],[f39,f210])).

fof(f210,plain,
    ( k1_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_3
  <=> k1_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f218,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl4_4 ),
    inference(resolution,[],[f214,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f214,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK3(u1_struct_0(sK0))))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl4_4
  <=> r1_tarski(k1_xboole_0,k1_tarski(sK3(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f215,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f206,f212,f208])).

fof(f206,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK3(u1_struct_0(sK0))))
    | k1_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0))) ),
    inference(resolution,[],[f202,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f202,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_tarski(k1_xboole_0,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(global_subsumption,[],[f117,f197])).

fof(f197,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(X0)
      | ~ r1_tarski(k1_xboole_0,k1_tarski(X0))
      | ~ v2_tex_2(k1_tarski(X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f157,f139])).

fof(f139,plain,(
    ! [X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f72,f137])).

fof(f137,plain,(
    ! [X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f54,f93])).

fof(f93,plain,(
    ! [X1] :
      ( k1_tarski(X1) = k6_domain_1(u1_struct_0(sK0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f72,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f72,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f57,f62])).

fof(f62,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f37,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f57,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f35,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | ~ r1_tarski(k1_xboole_0,X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f156,f56])).

fof(f56,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f32,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f32,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f156,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f75,f56])).

fof(f75,plain,(
    ! [X0] :
      ( sK1 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(global_subsumption,[],[f33,f37,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ r1_tarski(sK1,X0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f34,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_tex_2(k1_tarski(X0),sK0) ) ),
    inference(global_subsumption,[],[f72,f111])).

fof(f111,plain,(
    ! [X0] :
      ( v2_tex_2(k1_tarski(X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( v2_tex_2(k1_tarski(X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f59,f53])).

fof(f59,plain,(
    ! [X0] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f37,f36,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f35,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (825950208)
% 0.14/0.38  ipcrm: permission denied for id (825982988)
% 0.14/0.39  ipcrm: permission denied for id (826081300)
% 0.14/0.40  ipcrm: permission denied for id (826114079)
% 0.14/0.41  ipcrm: permission denied for id (826245158)
% 0.22/0.42  ipcrm: permission denied for id (826277937)
% 0.22/0.44  ipcrm: permission denied for id (826310720)
% 0.22/0.44  ipcrm: permission denied for id (826343489)
% 0.22/0.45  ipcrm: permission denied for id (826409033)
% 0.22/0.47  ipcrm: permission denied for id (826474582)
% 0.22/0.47  ipcrm: permission denied for id (826572889)
% 0.22/0.48  ipcrm: permission denied for id (826540125)
% 0.22/0.49  ipcrm: permission denied for id (826671212)
% 0.22/0.50  ipcrm: permission denied for id (826736755)
% 0.82/0.63  % (21969)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.17/0.64  % (21969)Refutation not found, incomplete strategy% (21969)------------------------------
% 1.17/0.64  % (21969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.64  % (21969)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.64  
% 1.17/0.64  % (21969)Memory used [KB]: 6140
% 1.17/0.64  % (21969)Time elapsed: 0.082 s
% 1.17/0.64  % (21969)------------------------------
% 1.17/0.64  % (21969)------------------------------
% 1.17/0.65  % (21977)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.17/0.65  % (21970)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.17/0.65  % (21977)Refutation not found, incomplete strategy% (21977)------------------------------
% 1.17/0.65  % (21977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.65  % (21977)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.65  
% 1.17/0.65  % (21977)Memory used [KB]: 6140
% 1.17/0.65  % (21977)Time elapsed: 0.097 s
% 1.17/0.65  % (21977)------------------------------
% 1.17/0.65  % (21977)------------------------------
% 1.17/0.65  % (21984)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.17/0.65  % (21966)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.17/0.65  % (21983)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.17/0.66  % (21967)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.17/0.66  % (21984)Refutation found. Thanks to Tanya!
% 1.17/0.66  % SZS status Theorem for theBenchmark
% 1.17/0.66  % SZS output start Proof for theBenchmark
% 1.17/0.66  fof(f238,plain,(
% 1.17/0.66    $false),
% 1.17/0.66    inference(avatar_sat_refutation,[],[f215,f218,f237])).
% 1.17/0.66  fof(f237,plain,(
% 1.17/0.66    ~spl4_3),
% 1.17/0.66    inference(avatar_contradiction_clause,[],[f232])).
% 1.17/0.66  fof(f232,plain,(
% 1.17/0.66    $false | ~spl4_3),
% 1.17/0.66    inference(subsumption_resolution,[],[f38,f221])).
% 1.17/0.66  fof(f221,plain,(
% 1.17/0.66    ~v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 1.17/0.66    inference(superposition,[],[f39,f210])).
% 1.17/0.66  fof(f210,plain,(
% 1.17/0.66    k1_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0))) | ~spl4_3),
% 1.17/0.66    inference(avatar_component_clause,[],[f208])).
% 1.17/0.66  fof(f208,plain,(
% 1.17/0.66    spl4_3 <=> k1_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0)))),
% 1.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.17/0.66  fof(f39,plain,(
% 1.17/0.66    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.17/0.66    inference(cnf_transformation,[],[f4])).
% 1.17/0.66  fof(f4,axiom,(
% 1.17/0.66    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.17/0.66  fof(f38,plain,(
% 1.17/0.66    v1_xboole_0(k1_xboole_0)),
% 1.17/0.66    inference(cnf_transformation,[],[f1])).
% 1.17/0.66  fof(f1,axiom,(
% 1.17/0.66    v1_xboole_0(k1_xboole_0)),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.17/0.66  fof(f218,plain,(
% 1.17/0.66    spl4_4),
% 1.17/0.66    inference(avatar_contradiction_clause,[],[f216])).
% 1.17/0.66  fof(f216,plain,(
% 1.17/0.66    $false | spl4_4),
% 1.17/0.66    inference(resolution,[],[f214,f40])).
% 1.17/0.66  fof(f40,plain,(
% 1.17/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.17/0.66    inference(cnf_transformation,[],[f3])).
% 1.17/0.66  fof(f3,axiom,(
% 1.17/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.17/0.66  fof(f214,plain,(
% 1.17/0.66    ~r1_tarski(k1_xboole_0,k1_tarski(sK3(u1_struct_0(sK0)))) | spl4_4),
% 1.17/0.66    inference(avatar_component_clause,[],[f212])).
% 1.17/0.66  fof(f212,plain,(
% 1.17/0.66    spl4_4 <=> r1_tarski(k1_xboole_0,k1_tarski(sK3(u1_struct_0(sK0))))),
% 1.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.17/0.66  fof(f215,plain,(
% 1.17/0.66    spl4_3 | ~spl4_4),
% 1.17/0.66    inference(avatar_split_clause,[],[f206,f212,f208])).
% 1.17/0.66  fof(f206,plain,(
% 1.17/0.66    ~r1_tarski(k1_xboole_0,k1_tarski(sK3(u1_struct_0(sK0)))) | k1_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0)))),
% 1.17/0.66    inference(resolution,[],[f202,f52])).
% 1.17/0.66  fof(f52,plain,(
% 1.17/0.66    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 1.17/0.66    inference(cnf_transformation,[],[f5])).
% 1.17/0.66  fof(f5,axiom,(
% 1.17/0.66    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.17/0.66  fof(f202,plain,(
% 1.17/0.66    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_tarski(k1_xboole_0,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.17/0.66    inference(global_subsumption,[],[f117,f197])).
% 1.17/0.66  fof(f197,plain,(
% 1.17/0.66    ( ! [X0] : (k1_xboole_0 = k1_tarski(X0) | ~r1_tarski(k1_xboole_0,k1_tarski(X0)) | ~v2_tex_2(k1_tarski(X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.17/0.66    inference(resolution,[],[f157,f139])).
% 1.17/0.66  fof(f139,plain,(
% 1.17/0.66    ( ! [X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.17/0.66    inference(global_subsumption,[],[f72,f137])).
% 1.17/0.66  fof(f137,plain,(
% 1.17/0.66    ( ! [X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.17/0.66    inference(duplicate_literal_removal,[],[f134])).
% 1.17/0.66  fof(f134,plain,(
% 1.17/0.66    ( ! [X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.17/0.66    inference(superposition,[],[f54,f93])).
% 1.17/0.66  fof(f93,plain,(
% 1.17/0.66    ( ! [X1] : (k1_tarski(X1) = k6_domain_1(u1_struct_0(sK0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.17/0.66    inference(resolution,[],[f72,f53])).
% 1.17/0.66  fof(f53,plain,(
% 1.17/0.66    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.17/0.66    inference(cnf_transformation,[],[f27])).
% 1.17/0.66  fof(f27,plain,(
% 1.17/0.66    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.17/0.66    inference(flattening,[],[f26])).
% 1.17/0.66  fof(f26,plain,(
% 1.17/0.66    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.17/0.66    inference(ennf_transformation,[],[f11])).
% 1.17/0.66  fof(f11,axiom,(
% 1.17/0.66    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.17/0.66  fof(f54,plain,(
% 1.17/0.66    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.17/0.66    inference(cnf_transformation,[],[f29])).
% 1.17/0.66  fof(f29,plain,(
% 1.17/0.66    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.17/0.66    inference(flattening,[],[f28])).
% 1.17/0.66  fof(f28,plain,(
% 1.17/0.66    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.17/0.66    inference(ennf_transformation,[],[f10])).
% 1.17/0.66  fof(f10,axiom,(
% 1.17/0.66    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.17/0.66  fof(f72,plain,(
% 1.17/0.66    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.17/0.66    inference(global_subsumption,[],[f57,f62])).
% 1.17/0.66  fof(f62,plain,(
% 1.17/0.66    l1_struct_0(sK0)),
% 1.17/0.66    inference(resolution,[],[f37,f42])).
% 1.17/0.66  fof(f42,plain,(
% 1.17/0.66    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.17/0.66    inference(cnf_transformation,[],[f18])).
% 1.17/0.66  fof(f18,plain,(
% 1.17/0.66    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.17/0.66    inference(ennf_transformation,[],[f8])).
% 1.17/0.66  fof(f8,axiom,(
% 1.17/0.66    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.17/0.66  fof(f37,plain,(
% 1.17/0.66    l1_pre_topc(sK0)),
% 1.17/0.66    inference(cnf_transformation,[],[f17])).
% 1.17/0.66  fof(f17,plain,(
% 1.17/0.66    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.17/0.66    inference(flattening,[],[f16])).
% 1.17/0.66  fof(f16,plain,(
% 1.17/0.66    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.17/0.66    inference(ennf_transformation,[],[f15])).
% 1.17/0.66  fof(f15,negated_conjecture,(
% 1.17/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.17/0.66    inference(negated_conjecture,[],[f14])).
% 1.17/0.66  fof(f14,conjecture,(
% 1.17/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 1.17/0.66  fof(f57,plain,(
% 1.17/0.66    ~l1_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 1.17/0.66    inference(resolution,[],[f35,f51])).
% 1.17/0.66  fof(f51,plain,(
% 1.17/0.66    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 1.17/0.66    inference(cnf_transformation,[],[f25])).
% 1.17/0.66  fof(f25,plain,(
% 1.17/0.66    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.17/0.66    inference(flattening,[],[f24])).
% 1.17/0.66  fof(f24,plain,(
% 1.17/0.66    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.17/0.66    inference(ennf_transformation,[],[f9])).
% 1.17/0.66  fof(f9,axiom,(
% 1.17/0.66    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.17/0.66  fof(f35,plain,(
% 1.17/0.66    ~v2_struct_0(sK0)),
% 1.17/0.66    inference(cnf_transformation,[],[f17])).
% 1.17/0.66  fof(f157,plain,(
% 1.17/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | ~r1_tarski(k1_xboole_0,X0) | ~v2_tex_2(X0,sK0)) )),
% 1.17/0.66    inference(forward_demodulation,[],[f156,f56])).
% 1.17/0.66  fof(f56,plain,(
% 1.17/0.66    k1_xboole_0 = sK1),
% 1.17/0.66    inference(resolution,[],[f32,f49])).
% 1.17/0.66  fof(f49,plain,(
% 1.17/0.66    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.17/0.66    inference(cnf_transformation,[],[f21])).
% 1.17/0.66  fof(f21,plain,(
% 1.17/0.66    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.17/0.66    inference(ennf_transformation,[],[f2])).
% 1.17/0.66  fof(f2,axiom,(
% 1.17/0.66    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.17/0.66  fof(f32,plain,(
% 1.17/0.66    v1_xboole_0(sK1)),
% 1.17/0.66    inference(cnf_transformation,[],[f17])).
% 1.17/0.66  fof(f156,plain,(
% 1.17/0.66    ( ! [X0] : (k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0)) )),
% 1.17/0.66    inference(forward_demodulation,[],[f75,f56])).
% 1.17/0.66  fof(f75,plain,(
% 1.17/0.66    ( ! [X0] : (sK1 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0)) )),
% 1.17/0.66    inference(global_subsumption,[],[f33,f37,f73])).
% 1.17/0.66  fof(f73,plain,(
% 1.17/0.66    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~r1_tarski(sK1,X0) | sK1 = X0) )),
% 1.17/0.66    inference(resolution,[],[f34,f47])).
% 1.17/0.66  fof(f47,plain,(
% 1.17/0.66    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X2,X0) | ~r1_tarski(X1,X2) | X1 = X2 | ~v3_tex_2(X1,X0)) )),
% 1.17/0.66    inference(cnf_transformation,[],[f20])).
% 1.17/0.66  fof(f20,plain,(
% 1.17/0.66    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.66    inference(flattening,[],[f19])).
% 1.17/0.66  fof(f19,plain,(
% 1.17/0.66    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.17/0.66    inference(ennf_transformation,[],[f12])).
% 1.17/0.66  fof(f12,axiom,(
% 1.17/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 1.17/0.66  fof(f34,plain,(
% 1.17/0.66    v3_tex_2(sK1,sK0)),
% 1.17/0.66    inference(cnf_transformation,[],[f17])).
% 1.17/0.66  fof(f33,plain,(
% 1.17/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.17/0.66    inference(cnf_transformation,[],[f17])).
% 1.17/0.66  fof(f117,plain,(
% 1.17/0.66    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_tex_2(k1_tarski(X0),sK0)) )),
% 1.17/0.66    inference(global_subsumption,[],[f72,f111])).
% 1.17/0.66  fof(f111,plain,(
% 1.17/0.66    ( ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 1.17/0.66    inference(duplicate_literal_removal,[],[f110])).
% 1.17/0.66  fof(f110,plain,(
% 1.17/0.66    ( ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.17/0.66    inference(superposition,[],[f59,f53])).
% 1.17/0.66  fof(f59,plain,(
% 1.17/0.66    ( ! [X0] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.17/0.66    inference(global_subsumption,[],[f37,f36,f58])).
% 1.17/0.66  fof(f58,plain,(
% 1.17/0.66    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)) )),
% 1.17/0.66    inference(resolution,[],[f35,f50])).
% 1.17/0.66  fof(f50,plain,(
% 1.17/0.66    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 1.17/0.66    inference(cnf_transformation,[],[f23])).
% 1.17/0.66  fof(f23,plain,(
% 1.17/0.66    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.17/0.66    inference(flattening,[],[f22])).
% 1.17/0.66  fof(f22,plain,(
% 1.17/0.66    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.17/0.66    inference(ennf_transformation,[],[f13])).
% 1.17/0.66  fof(f13,axiom,(
% 1.17/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 1.17/0.66  fof(f36,plain,(
% 1.17/0.66    v2_pre_topc(sK0)),
% 1.17/0.66    inference(cnf_transformation,[],[f17])).
% 1.17/0.66  % SZS output end Proof for theBenchmark
% 1.17/0.66  % (21984)------------------------------
% 1.17/0.66  % (21984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.66  % (21984)Termination reason: Refutation
% 1.17/0.66  
% 1.17/0.66  % (21984)Memory used [KB]: 10874
% 1.17/0.66  % (21984)Time elapsed: 0.096 s
% 1.17/0.66  % (21984)------------------------------
% 1.17/0.66  % (21984)------------------------------
% 1.17/0.66  % (21764)Success in time 0.303 s
%------------------------------------------------------------------------------
