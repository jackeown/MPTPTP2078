%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1372+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:19 EST 2020

% Result     : Theorem 2.55s
% Output     : Refutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   28 (  53 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 193 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7957,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7956,f5271])).

fof(f5271,plain,(
    l1_pre_topc(sK72) ),
    inference(cnf_transformation,[],[f4193])).

fof(f4193,plain,
    ( ~ v1_compts_1(sK72)
    & v1_finset_1(u1_struct_0(sK72))
    & l1_pre_topc(sK72)
    & v2_pre_topc(sK72) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK72])],[f2534,f4192])).

fof(f4192,plain,
    ( ? [X0] :
        ( ~ v1_compts_1(X0)
        & v1_finset_1(u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ~ v1_compts_1(sK72)
      & v1_finset_1(u1_struct_0(sK72))
      & l1_pre_topc(sK72)
      & v2_pre_topc(sK72) ) ),
    introduced(choice_axiom,[])).

fof(f2534,plain,(
    ? [X0] :
      ( ~ v1_compts_1(X0)
      & v1_finset_1(u1_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2533])).

fof(f2533,plain,(
    ? [X0] :
      ( ~ v1_compts_1(X0)
      & v1_finset_1(u1_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2489])).

fof(f2489,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( v1_finset_1(u1_struct_0(X0))
         => v1_compts_1(X0) ) ) ),
    inference(negated_conjecture,[],[f2488])).

fof(f2488,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_finset_1(u1_struct_0(X0))
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_compts_1)).

fof(f7956,plain,(
    ~ l1_pre_topc(sK72) ),
    inference(subsumption_resolution,[],[f7955,f5273])).

fof(f5273,plain,(
    ~ v1_compts_1(sK72) ),
    inference(cnf_transformation,[],[f4193])).

fof(f7955,plain,
    ( v1_compts_1(sK72)
    | ~ l1_pre_topc(sK72) ),
    inference(subsumption_resolution,[],[f7954,f5270])).

fof(f5270,plain,(
    v2_pre_topc(sK72) ),
    inference(cnf_transformation,[],[f4193])).

fof(f7954,plain,
    ( ~ v2_pre_topc(sK72)
    | v1_compts_1(sK72)
    | ~ l1_pre_topc(sK72) ),
    inference(resolution,[],[f7930,f5311])).

fof(f5311,plain,(
    ! [X0] :
      ( ~ v8_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2555])).

fof(f2555,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
        & v2_pre_topc(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2554])).

fof(f2554,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
        & v2_pre_topc(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2439])).

fof(f2439,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v8_struct_0(X0) )
       => ( v1_compts_1(X0)
          & v2_pre_topc(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_compts_1)).

fof(f7930,plain,(
    v8_struct_0(sK72) ),
    inference(subsumption_resolution,[],[f7924,f7916])).

fof(f7916,plain,(
    l1_struct_0(sK72) ),
    inference(resolution,[],[f5271,f7514])).

fof(f7514,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3937])).

fof(f3937,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f7924,plain,
    ( ~ l1_struct_0(sK72)
    | v8_struct_0(sK72) ),
    inference(resolution,[],[f5272,f6666])).

fof(f6666,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3451])).

fof(f3451,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(flattening,[],[f3450])).

fof(f3450,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1807])).

fof(f1807,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v8_struct_0(X0) )
     => ~ v1_finset_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_struct_0)).

fof(f5272,plain,(
    v1_finset_1(u1_struct_0(sK72)) ),
    inference(cnf_transformation,[],[f4193])).
%------------------------------------------------------------------------------
