%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 (1162 expanded)
%              Number of leaves         :   15 ( 302 expanded)
%              Depth                    :   25
%              Number of atoms          :  395 (6671 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f274,plain,(
    $false ),
    inference(resolution,[],[f269,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f269,plain,(
    ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f268,f150])).

fof(f150,plain,(
    ! [X0] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f149,f135])).

fof(f135,plain,(
    ~ v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f133,f124])).

fof(f124,plain,(
    ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f123,f109])).

fof(f109,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f108,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f108,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f86])).

fof(f86,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f45,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f46,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f123,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f122,f44])).

fof(f122,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f121,f45])).

fof(f121,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f120,f115])).

fof(f115,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f114,f44])).

fof(f114,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f45])).

fof(f103,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f46,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f120,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f118,f111])).

fof(f111,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f110,f44])).

fof(f110,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f101,f45])).

fof(f101,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f46,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f118,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f47,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f47,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f133,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v7_struct_0(sK0) ),
    inference(resolution,[],[f86,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f149,plain,(
    ! [X0] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_zfmisc_1(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f134,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f134,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f132,f44])).

fof(f132,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f86,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f268,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f267,f235])).

fof(f235,plain,(
    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f231,f167])).

fof(f167,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f163,f45])).

fof(f163,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f115,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f231,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f229,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f229,plain,(
    ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f228,f134])).

fof(f228,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f227,f135])).

fof(f227,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f226,f46])).

fof(f226,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f223,f167])).

fof(f223,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f130,f54])).

fof(f130,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f129,f45])).

fof(f129,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f128,f115])).

fof(f128,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f48,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(X2,u1_struct_0(X0))
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f48,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f267,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tex_2(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f243,f169])).

fof(f169,plain,(
    l1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f159,f49])).

fof(f159,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f115,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f45,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

% (24149)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f18,plain,(
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

fof(f243,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tex_2(sK0,sK1)))
      | ~ l1_struct_0(k1_tex_2(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f147,f235])).

fof(f147,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),X0),u1_struct_0(k1_tex_2(sK0,sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tex_2(sK0,sK1)))
      | ~ l1_struct_0(k1_tex_2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f138,f117])).

fof(f117,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f116,f44])).

fof(f116,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f105,f45])).

fof(f105,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f46,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f138,plain,(
    ! [X0] :
      ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),X0),u1_struct_0(k1_tex_2(sK0,sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tex_2(sK0,sK1)))
      | ~ l1_struct_0(k1_tex_2(sK0,sK1)) ) ),
    inference(resolution,[],[f111,f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (24144)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (24141)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (24141)Refutation not found, incomplete strategy% (24141)------------------------------
% 0.21/0.47  % (24141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24135)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (24135)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f274,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(resolution,[],[f269,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f13])).
% 0.21/0.47  fof(f13,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.21/0.47  fof(f269,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f268,f150])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ( ! [X0] : (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f149,f135])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    ~v1_zfmisc_1(u1_struct_0(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f133,f124])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ~v7_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f123,f109])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ~v7_struct_0(sK0) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f108,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ~v7_struct_0(sK0) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f100,f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    l1_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f45,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    ~v7_struct_0(sK0) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f46,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v7_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f122,f44])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f121,f45])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f120,f115])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f114,f44])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f103,f45])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f46,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f118,f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f110,f44])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ~v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f101,f45])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f46,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f47,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    ~v1_zfmisc_1(u1_struct_0(sK0)) | v7_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f86,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ( ! [X0] : (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0))) )),
% 0.21/0.47    inference(resolution,[],[f134,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f132,f44])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ~v1_xboole_0(u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f86,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.47  fof(f268,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f267,f235])).
% 0.21/0.47  fof(f235,plain,(
% 0.21/0.47    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f231,f167])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f163,f45])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.47    inference(resolution,[],[f115,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.47  fof(f231,plain,(
% 0.21/0.47    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(resolution,[],[f229,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f228,f134])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f227,f135])).
% 0.21/0.47  fof(f227,plain,(
% 0.21/0.47    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f226,f46])).
% 0.21/0.47  fof(f226,plain,(
% 0.21/0.47    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f223,f167])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.47    inference(resolution,[],[f130,f54])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f129,f45])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f128,f115])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.47    inference(resolution,[],[f48,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) & (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(k1_tex_2(sK0,sK1)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f243,f169])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f159,f49])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f115,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.21/0.48    inference(resolution,[],[f45,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  % (24149)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_struct_0(k1_tex_2(sK0,sK1))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f147,f235])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),X0),u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_subset_1(X0,u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_struct_0(k1_tex_2(sK0,sK1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f138,f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f116,f44])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    v7_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f45])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    v7_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f46,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ( ! [X0] : (~v7_struct_0(k1_tex_2(sK0,sK1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),X0),u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_subset_1(X0,u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_struct_0(k1_tex_2(sK0,sK1))) )),
% 0.21/0.48    inference(resolution,[],[f111,f57])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (24135)------------------------------
% 0.21/0.48  % (24135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24135)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (24135)Memory used [KB]: 1663
% 0.21/0.48  % (24135)Time elapsed: 0.057 s
% 0.21/0.48  % (24135)------------------------------
% 0.21/0.48  % (24135)------------------------------
% 0.21/0.48  % (24141)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (24141)Memory used [KB]: 6140
% 0.21/0.48  % (24141)Time elapsed: 0.045 s
% 0.21/0.48  % (24141)------------------------------
% 0.21/0.48  % (24141)------------------------------
% 0.21/0.48  % (24124)Success in time 0.125 s
%------------------------------------------------------------------------------
