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
% DateTime   : Thu Dec  3 13:20:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 684 expanded)
%              Number of leaves         :   15 ( 179 expanded)
%              Depth                    :   21
%              Number of atoms          :  434 (4058 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f270,plain,(
    $false ),
    inference(subsumption_resolution,[],[f266,f176])).

fof(f176,plain,(
    v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f175,f128])).

fof(f128,plain,
    ( v7_struct_0(sK0)
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f127,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
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

fof(f38,plain,
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

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(f127,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f126,f87])).

fof(f87,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f45,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f126,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f125,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f125,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f48,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

fof(f48,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f175,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f174,f44])).

fof(f174,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f173,f45])).

fof(f173,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f172,f115])).

fof(f115,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f114,f44])).

fof(f114,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f104,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f46,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f172,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f121])).

fof(f121,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f120,f44])).

fof(f120,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f108,f45])).

fof(f108,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f46,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f166,plain,
    ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f119,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X1)
      | v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | v1_tex_2(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | v1_tex_2(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc13_tex_2)).

fof(f119,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f118,f44])).

fof(f118,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f106,f45])).

fof(f106,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f46,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f266,plain,(
    ~ v7_struct_0(sK0) ),
    inference(resolution,[],[f265,f113])).

fof(f113,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f112,f44])).

fof(f112,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f87])).

fof(f103,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f46,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(f265,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f264,f44])).

fof(f264,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f263,f176])).

fof(f263,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f262,f87])).

fof(f262,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f261,f226])).

fof(f226,plain,(
    ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f220,f115])).

fof(f220,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f191,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f191,plain,(
    l1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f160,f49])).

fof(f160,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f119,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f45,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f261,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f260,f168])).

fof(f168,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f162,f45])).

fof(f162,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f119,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f260,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f124,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ v1_xboole_0(X1)
           => ( ~ v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tex_2)).

fof(f124,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f123,f45])).

fof(f123,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f122,f119])).

fof(f122,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f47,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f47,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:24:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (2395)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (2394)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (2391)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (2394)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f270,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f266,f176])).
% 0.22/0.48  fof(f176,plain,(
% 0.22/0.48    v7_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f175,f128])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    v7_struct_0(sK0) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f127,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f12])).
% 0.22/0.48  fof(f12,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f126,f87])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    l1_struct_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f45,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f39])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_struct_0(sK0) | v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f125,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f39])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f48,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f39])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v7_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f174,f44])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f173,f45])).
% 0.22/0.48  fof(f173,plain,(
% 0.22/0.48    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f172,f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f114,f44])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    ~v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f104,f45])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f46,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f166,f121])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.48    inference(subsumption_resolution,[],[f120,f44])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    v7_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f108,f45])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    v7_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f46,f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    ~v7_struct_0(k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f119,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v7_struct_0(X1) | v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v7_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((~v7_struct_0(X1) & ~v2_struct_0(X1)) | v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((~v7_struct_0(X1) & ~v2_struct_0(X1)) | (v1_tex_2(X1,X0) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) => (~v7_struct_0(X1) & ~v2_struct_0(X1)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc13_tex_2)).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f118,f44])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f106,f45])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f46,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f266,plain,(
% 0.22/0.48    ~v7_struct_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f265,f113])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v7_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f112,f44])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    ~v7_struct_0(sK0) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f103,f87])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ~v7_struct_0(sK0) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f46,f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).
% 0.22/0.48  fof(f265,plain,(
% 0.22/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f264,f44])).
% 0.22/0.48  fof(f264,plain,(
% 0.22/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f263,f176])).
% 0.22/0.48  fof(f263,plain,(
% 0.22/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f262,f87])).
% 0.22/0.48  fof(f262,plain,(
% 0.22/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | ~v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f261,f226])).
% 0.22/0.48  fof(f226,plain,(
% 0.22/0.48    ~v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f220,f115])).
% 0.22/0.48  fof(f220,plain,(
% 0.22/0.48    ~v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f191,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.48  fof(f191,plain,(
% 0.22/0.48    l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f160,f49])).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f119,f88])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.22/0.48    inference(resolution,[],[f45,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.48  fof(f261,plain,(
% 0.22/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_struct_0(sK0) | ~v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f260,f168])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f162,f45])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.48    inference(resolution,[],[f119,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.48  fof(f260,plain,(
% 0.22/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_struct_0(sK0) | ~v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f259])).
% 0.22/0.48  fof(f259,plain,(
% 0.22/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | ~v7_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f124,f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_subset_1(X1,u1_struct_0(X0)) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~v1_xboole_0(X1) => (~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tex_2)).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f123,f45])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f122,f119])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.48    inference(resolution,[],[f47,f69])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(rectify,[],[f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f39])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (2394)------------------------------
% 0.22/0.48  % (2394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (2394)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (2394)Memory used [KB]: 1663
% 0.22/0.48  % (2394)Time elapsed: 0.057 s
% 0.22/0.48  % (2394)------------------------------
% 0.22/0.48  % (2394)------------------------------
% 0.22/0.48  % (2386)Success in time 0.12 s
%------------------------------------------------------------------------------
