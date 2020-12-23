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
% DateTime   : Thu Dec  3 13:20:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  121 (2874 expanded)
%              Number of leaves         :   18 ( 757 expanded)
%              Depth                    :   37
%              Number of atoms          :  469 (16365 expanded)
%              Number of equality atoms :   61 ( 490 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f370,plain,(
    $false ),
    inference(global_subsumption,[],[f103,f354,f366])).

fof(f366,plain,(
    ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f56,f57,f95,f96,f354,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f96,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f56,f57,f58,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f58,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,
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

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f95,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f56,f57,f58,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f354,plain,(
    v7_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f85,f296,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f296,plain,(
    v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f115,f293])).

fof(f293,plain,(
    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f292,f249])).

fof(f249,plain,
    ( v7_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f246,f85])).

fof(f246,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | v7_struct_0(sK0) ),
    inference(resolution,[],[f245,f70])).

fof(f245,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f244,f92])).

fof(f92,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f56,f85,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f244,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f240,f58])).

fof(f240,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f239])).

fof(f239,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(superposition,[],[f63,f231])).

fof(f231,plain,
    ( u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f230,f228])).

fof(f228,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f227,f188])).

fof(f188,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f127,f60])).

fof(f60,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f127,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f97,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f97,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f92,f58,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f227,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f226,f57])).

fof(f226,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f222,f96])).

fof(f222,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    inference(superposition,[],[f69,f195])).

fof(f195,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f194,f96])).

fof(f194,plain,
    ( u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f188,f88])).

fof(f88,plain,(
    ! [X2] :
      ( v1_tex_2(X2,sK0)
      | ~ m1_pre_topc(X2,sK0)
      | u1_struct_0(X2) = sK3(sK0,X2) ) ),
    inference(resolution,[],[f57,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f230,plain,
    ( u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f225,f77])).

fof(f225,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f224,f188])).

fof(f224,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f223,f57])).

fof(f223,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f221,f96])).

fof(f221,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    inference(superposition,[],[f67,f195])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) != X0
      | v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f292,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f291,f96])).

fof(f291,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f288,f95])).

fof(f288,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(sK0) ),
    inference(resolution,[],[f257,f103])).

fof(f257,plain,(
    ! [X0] :
      ( ~ v1_tex_2(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f256,f56])).

fof(f256,plain,(
    ! [X0] :
      ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ v1_tex_2(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f255,f57])).

fof(f255,plain,(
    ! [X0] :
      ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_tex_2(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f249,f74])).

fof(f115,plain,(
    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f94,f108,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f108,plain,(
    l1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f105,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f105,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f96,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f94,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f56,f57,f58,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f85,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f57,f64])).

fof(f103,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f56])).

fof(f102,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f101,f85])).

fof(f101,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f58])).

fof(f100,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f59,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f59,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:52:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (30473)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (30465)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (30460)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (30469)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (30473)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f370,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(global_subsumption,[],[f103,f354,f366])).
% 0.22/0.49  fof(f366,plain,(
% 0.22/0.49    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f56,f57,f95,f96,f354,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v7_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f56,f57,f58,f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f14])).
% 0.22/0.49  fof(f14,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f56,f57,f58,f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f39])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f46])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f46])).
% 0.22/0.49  fof(f354,plain,(
% 0.22/0.49    v7_struct_0(sK0)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f85,f296,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.22/0.49  fof(f296,plain,(
% 0.22/0.49    v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.49    inference(backward_demodulation,[],[f115,f293])).
% 0.22/0.49  fof(f293,plain,(
% 0.22/0.49    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f292,f249])).
% 0.22/0.49  fof(f249,plain,(
% 0.22/0.49    v7_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f246,f85])).
% 0.22/0.49  fof(f246,plain,(
% 0.22/0.49    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~l1_struct_0(sK0) | v7_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f245,f70])).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    v1_zfmisc_1(u1_struct_0(sK0)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f244,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f56,f85,f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.49  fof(f244,plain,(
% 0.22/0.49    v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f240,f58])).
% 0.22/0.49  fof(f240,plain,(
% 0.22/0.49    v1_zfmisc_1(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f239])).
% 0.22/0.49  fof(f239,plain,(
% 0.22/0.49    u1_struct_0(sK0) != u1_struct_0(sK0) | v1_zfmisc_1(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    inference(superposition,[],[f63,f231])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f230,f228])).
% 0.22/0.49  fof(f228,plain,(
% 0.22/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f227,f188])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.22/0.49    inference(resolution,[],[f127,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f46])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.22/0.49    inference(resolution,[],[f97,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(nnf_transformation,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f92,f58,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f226,f57])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f222,f96])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.22/0.49    inference(superposition,[],[f69,f195])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f194,f96])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f188,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X2] : (v1_tex_2(X2,sK0) | ~m1_pre_topc(X2,sK0) | u1_struct_0(X2) = sK3(sK0,X2)) )),
% 0.22/0.49    inference(resolution,[],[f57,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X1) = sK3(X0,X1) | ~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(rectify,[],[f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f54])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.49    inference(resolution,[],[f225,f77])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f224,f188])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f223,f57])).
% 0.22/0.49  fof(f223,plain,(
% 0.22/0.49    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f221,f96])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.22/0.49    inference(superposition,[],[f67,f195])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f54])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k6_domain_1(X0,X1) != X0 | v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.49    inference(rectify,[],[f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.22/0.49  fof(f292,plain,(
% 0.22/0.49    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f291,f96])).
% 0.22/0.49  fof(f291,plain,(
% 0.22/0.49    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f288,f95])).
% 0.22/0.49  fof(f288,plain,(
% 0.22/0.49    v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f257,f103])).
% 0.22/0.49  fof(f257,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_tex_2(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f256,f56])).
% 0.22/0.49  fof(f256,plain,(
% 0.22/0.49    ( ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~v1_tex_2(X0,sK0) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f255,f57])).
% 0.22/0.49  fof(f255,plain,(
% 0.22/0.49    ( ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v1_tex_2(X0,sK0) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(resolution,[],[f249,f74])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f94,f108,f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f105,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f57,f96,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f56,f57,f58,f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    l1_struct_0(sK0)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f57,f64])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v7_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f102,f56])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f101,f85])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f100,f58])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v7_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f59,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v7_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f46])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (30473)------------------------------
% 0.22/0.49  % (30473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (30473)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (30473)Memory used [KB]: 6396
% 0.22/0.49  % (30473)Time elapsed: 0.020 s
% 0.22/0.49  % (30473)------------------------------
% 0.22/0.49  % (30473)------------------------------
% 0.22/0.50  % (30453)Success in time 0.131 s
%------------------------------------------------------------------------------
