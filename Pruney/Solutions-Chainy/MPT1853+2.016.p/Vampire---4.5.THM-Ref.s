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
% DateTime   : Thu Dec  3 13:20:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  139 (8760 expanded)
%              Number of leaves         :   19 (2309 expanded)
%              Depth                    :   55
%              Number of atoms          :  544 (51313 expanded)
%              Number of equality atoms :   93 (1446 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(global_subsumption,[],[f98,f293,f301])).

fof(f301,plain,(
    ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f55,f56,f93,f94,f293,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f94,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f57,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(f93,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f293,plain,(
    v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f292,f84])).

fof(f84,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f56,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f292,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f285,f118])).

fof(f118,plain,(
    v1_zfmisc_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f61,f114,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_zfmisc_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_zfmisc_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_1)).

fof(f114,plain,(
    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f92,f107,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f107,plain,(
    l1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f105,f62])).

fof(f105,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f56,f94,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f92,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f285,plain,
    ( ~ v1_zfmisc_1(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v7_struct_0(sK0) ),
    inference(superposition,[],[f70,f254])).

fof(f254,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f253,f237])).

fof(f237,plain,
    ( v7_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f235,f84])).

fof(f235,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v7_struct_0(sK0) ),
    inference(resolution,[],[f213,f70])).

fof(f213,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f114,f207])).

fof(f207,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f206,f94])).

fof(f206,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f205,f93])).

fof(f205,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f200,f178])).

fof(f178,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f177,f174])).

fof(f174,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f173,f56])).

fof(f173,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f170,f94])).

fof(f170,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f67,f167])).

fof(f167,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f151])).

fof(f151,plain,
    ( v7_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f143,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f143,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v7_struct_0(sK0)
      | u1_struct_0(sK0) = X0
      | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ) ),
    inference(resolution,[],[f141,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f141,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f139,f84])).

fof(f139,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v7_struct_0(sK0) ),
    inference(resolution,[],[f133,f70])).

fof(f133,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f132,f94])).

fof(f132,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f87,f103])).

fof(f103,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f102,f57])).

fof(f102,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f59,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

fof(f59,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    ! [X2] :
      ( v1_tex_2(X2,sK0)
      | ~ m1_pre_topc(X2,sK0)
      | u1_struct_0(X2) = sK2(sK0,X2) ) ),
    inference(resolution,[],[f56,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f166,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f165,f94])).

fof(f165,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f162,f93])).

fof(f162,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v7_struct_0(sK0) ),
    inference(resolution,[],[f158,f98])).

fof(f158,plain,(
    ! [X1] :
      ( ~ v1_tex_2(X1,sK0)
      | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f55])).

fof(f157,plain,(
    ! [X1] :
      ( k1_xboole_0 = u1_struct_0(sK0)
      | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ v1_tex_2(X1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f56])).

fof(f156,plain,(
    ! [X1] :
      ( k1_xboole_0 = u1_struct_0(sK0)
      | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_tex_2(X1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f151,f73])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f177,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f172,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f172,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f171,f56])).

fof(f171,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f94])).

fof(f169,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f65,f167])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f200,plain,(
    ! [X1] :
      ( ~ v1_tex_2(X1,sK0)
      | k1_xboole_0 = u1_struct_0(sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f199,f55])).

fof(f199,plain,(
    ! [X1] :
      ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ v1_tex_2(X1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f198,f56])).

fof(f198,plain,(
    ! [X1] :
      ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_tex_2(X1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f196,f73])).

fof(f196,plain,
    ( v7_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v7_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f189,f60])).

fof(f189,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
      | v7_struct_0(sK0)
      | u1_struct_0(sK0) = X0
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f186,f81])).

fof(f186,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f184,f84])).

fof(f184,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v7_struct_0(sK0) ),
    inference(resolution,[],[f181,f70])).

fof(f181,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f178,f103])).

fof(f253,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f252,f94])).

fof(f252,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f248,f93])).

fof(f248,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v7_struct_0(sK0) ),
    inference(resolution,[],[f246,f98])).

fof(f246,plain,(
    ! [X1] :
      ( ~ v1_tex_2(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f245,f55])).

fof(f245,plain,(
    ! [X1] :
      ( k1_xboole_0 = u1_struct_0(sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ v1_tex_2(X1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f244,f56])).

fof(f244,plain,(
    ! [X1] :
      ( k1_xboole_0 = u1_struct_0(sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_tex_2(X1,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f237,f73])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f98,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f97,f55])).

fof(f97,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f96,f84])).

fof(f96,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f95,f57])).

fof(f95,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f58,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(f58,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:16:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (3820)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.43  % (3820)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f303,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(global_subsumption,[],[f98,f293,f301])).
% 0.21/0.43  fof(f301,plain,(
% 0.21/0.43    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f55,f56,f93,f94,f293,f73])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v7_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f35])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f55,f56,f57,f78])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.43    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.43  fof(f13,axiom,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f17])).
% 0.21/0.43  fof(f17,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f55,f56,f57,f77])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f41])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    l1_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f49])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ~v2_struct_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f49])).
% 0.21/0.43  fof(f293,plain,(
% 0.21/0.43    v7_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f292,f84])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    l1_struct_0(sK0)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f56,f62])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.43  fof(f292,plain,(
% 0.21/0.43    ~l1_struct_0(sK0) | v7_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f285,f118])).
% 0.21/0.43  fof(f118,plain,(
% 0.21/0.43    v1_zfmisc_1(k1_xboole_0)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f61,f114,f68])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_zfmisc_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : (v1_zfmisc_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_zfmisc_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_1)).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f92,f107,f74])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f105,f62])).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f56,f94,f63])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f55,f56,f57,f80])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.43    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.43  fof(f14,axiom,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.43  fof(f285,plain,(
% 0.21/0.43    ~v1_zfmisc_1(k1_xboole_0) | ~l1_struct_0(sK0) | v7_struct_0(sK0)),
% 0.21/0.43    inference(superposition,[],[f70,f254])).
% 0.21/0.43  fof(f254,plain,(
% 0.21/0.43    k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f253,f237])).
% 0.21/0.43  fof(f237,plain,(
% 0.21/0.43    v7_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f235,f84])).
% 0.21/0.43  fof(f235,plain,(
% 0.21/0.43    k1_xboole_0 = u1_struct_0(sK0) | ~l1_struct_0(sK0) | v7_struct_0(sK0)),
% 0.21/0.43    inference(resolution,[],[f213,f70])).
% 0.21/0.43  fof(f213,plain,(
% 0.21/0.43    v1_zfmisc_1(u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(superposition,[],[f114,f207])).
% 0.21/0.43  fof(f207,plain,(
% 0.21/0.43    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f206,f94])).
% 0.21/0.43  fof(f206,plain,(
% 0.21/0.43    k1_xboole_0 = u1_struct_0(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.43    inference(subsumption_resolution,[],[f205,f93])).
% 0.21/0.43  fof(f205,plain,(
% 0.21/0.43    k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f201])).
% 0.21/0.43  fof(f201,plain,(
% 0.21/0.43    k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.43    inference(resolution,[],[f200,f178])).
% 0.21/0.43  fof(f178,plain,(
% 0.21/0.43    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.43    inference(subsumption_resolution,[],[f177,f174])).
% 0.21/0.43  fof(f174,plain,(
% 0.21/0.43    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f173,f56])).
% 0.21/0.43  fof(f173,plain,(
% 0.21/0.43    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f170,f94])).
% 0.21/0.43  fof(f170,plain,(
% 0.21/0.43    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(superposition,[],[f67,f167])).
% 0.21/0.43  fof(f167,plain,(
% 0.21/0.43    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f166,f151])).
% 0.21/0.43  fof(f151,plain,(
% 0.21/0.43    v7_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.21/0.43    inference(resolution,[],[f143,f60])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f143,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(X0) | v7_struct_0(sK0) | u1_struct_0(sK0) = X0 | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))) )),
% 0.21/0.43    inference(resolution,[],[f141,f81])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.43  fof(f141,plain,(
% 0.21/0.43    v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v7_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f139,f84])).
% 0.21/0.43  fof(f139,plain,(
% 0.21/0.43    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v7_struct_0(sK0)),
% 0.21/0.43    inference(resolution,[],[f133,f70])).
% 0.21/0.43  fof(f133,plain,(
% 0.21/0.43    v1_zfmisc_1(u1_struct_0(sK0)) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.43    inference(subsumption_resolution,[],[f132,f94])).
% 0.21/0.43  fof(f132,plain,(
% 0.21/0.43    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.43    inference(resolution,[],[f87,f103])).
% 0.21/0.43  fof(f103,plain,(
% 0.21/0.43    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.43    inference(subsumption_resolution,[],[f102,f57])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.43    inference(resolution,[],[f59,f69])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.43    inference(flattening,[],[f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,axiom,(
% 0.21/0.43    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f49])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    ( ! [X2] : (v1_tex_2(X2,sK0) | ~m1_pre_topc(X2,sK0) | u1_struct_0(X2) = sK2(sK0,X2)) )),
% 0.21/0.43    inference(resolution,[],[f56,f66])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f53])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(rectify,[],[f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(flattening,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,axiom,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.21/0.43  fof(f166,plain,(
% 0.21/0.43    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | ~v7_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f165,f94])).
% 0.21/0.43  fof(f165,plain,(
% 0.21/0.43    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | k1_xboole_0 = u1_struct_0(sK0) | ~v7_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f162,f93])).
% 0.21/0.43  fof(f162,plain,(
% 0.21/0.43    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | k1_xboole_0 = u1_struct_0(sK0) | ~v7_struct_0(sK0)),
% 0.21/0.43    inference(resolution,[],[f158,f98])).
% 0.21/0.43  fof(f158,plain,(
% 0.21/0.43    ( ! [X1] : (~v1_tex_2(X1,sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f157,f55])).
% 0.21/0.43  fof(f157,plain,(
% 0.21/0.43    ( ! [X1] : (k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~v1_tex_2(X1,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f156,f56])).
% 0.21/0.43  fof(f156,plain,(
% 0.21/0.43    ( ! [X1] : (k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0) | ~v1_tex_2(X1,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(resolution,[],[f151,f73])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f53])).
% 0.21/0.43  fof(f177,plain,(
% 0.21/0.43    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.21/0.43    inference(resolution,[],[f172,f76])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f171,f56])).
% 0.21/0.43  fof(f171,plain,(
% 0.21/0.43    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f169,f94])).
% 0.21/0.43  fof(f169,plain,(
% 0.21/0.43    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(superposition,[],[f65,f167])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f53])).
% 0.21/0.43  fof(f200,plain,(
% 0.21/0.43    ( ! [X1] : (~v1_tex_2(X1,sK0) | k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f199,f55])).
% 0.21/0.43  fof(f199,plain,(
% 0.21/0.43    ( ! [X1] : (u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~v1_tex_2(X1,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f198,f56])).
% 0.21/0.43  fof(f198,plain,(
% 0.21/0.43    ( ! [X1] : (u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0) | ~v1_tex_2(X1,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(resolution,[],[f196,f73])).
% 0.21/0.43  fof(f196,plain,(
% 0.21/0.43    v7_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f191])).
% 0.21/0.43  fof(f191,plain,(
% 0.21/0.43    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v7_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.43    inference(resolution,[],[f189,f60])).
% 0.21/0.43  fof(f189,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(X0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v7_struct_0(sK0) | u1_struct_0(sK0) = X0 | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.21/0.43    inference(resolution,[],[f186,f81])).
% 0.21/0.43  fof(f186,plain,(
% 0.21/0.43    v1_xboole_0(u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v7_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f184,f84])).
% 0.21/0.43  fof(f184,plain,(
% 0.21/0.43    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v7_struct_0(sK0)),
% 0.21/0.43    inference(resolution,[],[f181,f70])).
% 0.21/0.43  fof(f181,plain,(
% 0.21/0.43    v1_zfmisc_1(u1_struct_0(sK0)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.43    inference(resolution,[],[f178,f103])).
% 0.21/0.43  fof(f253,plain,(
% 0.21/0.43    k1_xboole_0 = u1_struct_0(sK0) | ~v7_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f252,f94])).
% 0.21/0.43  fof(f252,plain,(
% 0.21/0.43    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | k1_xboole_0 = u1_struct_0(sK0) | ~v7_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f248,f93])).
% 0.21/0.43  fof(f248,plain,(
% 0.21/0.43    v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | k1_xboole_0 = u1_struct_0(sK0) | ~v7_struct_0(sK0)),
% 0.21/0.43    inference(resolution,[],[f246,f98])).
% 0.21/0.43  fof(f246,plain,(
% 0.21/0.43    ( ! [X1] : (~v1_tex_2(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f245,f55])).
% 0.21/0.43  fof(f245,plain,(
% 0.21/0.43    ( ! [X1] : (k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~v1_tex_2(X1,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f244,f56])).
% 0.21/0.43  fof(f244,plain,(
% 0.21/0.43    ( ! [X1] : (k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0) | ~v1_tex_2(X1,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.43    inference(resolution,[],[f237,f73])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v7_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f97,f55])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f96,f84])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f95,f57])).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v7_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(resolution,[],[f58,f71])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v7_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,axiom,(
% 0.21/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f49])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (3820)------------------------------
% 0.21/0.43  % (3820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (3820)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (3820)Memory used [KB]: 6268
% 0.21/0.43  % (3820)Time elapsed: 0.012 s
% 0.21/0.43  % (3820)------------------------------
% 0.21/0.43  % (3820)------------------------------
% 0.21/0.44  % (3804)Success in time 0.073 s
%------------------------------------------------------------------------------
