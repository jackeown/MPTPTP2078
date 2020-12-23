%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1372+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  53 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 193 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f16])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v1_compts_1(sK0)
    & v1_finset_1(u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ~ v1_compts_1(X0)
        & v1_finset_1(u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ~ v1_compts_1(sK0)
      & v1_finset_1(u1_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v1_compts_1(X0)
      & v1_finset_1(u1_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ~ v1_compts_1(X0)
      & v1_finset_1(u1_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( v1_finset_1(u1_struct_0(X0))
         => v1_compts_1(X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_finset_1(u1_struct_0(X0))
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_compts_1)).

fof(f28,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f27,f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f27,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f26,f17])).

fof(f17,plain,(
    v1_finset_1(u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_finset_1(u1_struct_0(sK0)) ),
    inference(resolution,[],[f25,f22])).

fof(f22,plain,(
    ! [X0] :
      ( v8_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_finset_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v8_struct_0(X0) )
     => ~ v1_finset_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_struct_0)).

fof(f25,plain,(
    ~ v8_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f24,f16])).

fof(f24,plain,
    ( ~ v8_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f23,f15])).

fof(f15,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v8_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f21,f18])).

fof(f18,plain,(
    ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
        & v2_pre_topc(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
        & v2_pre_topc(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v8_struct_0(X0) )
       => ( v1_compts_1(X0)
          & v2_pre_topc(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_compts_1)).

%------------------------------------------------------------------------------
