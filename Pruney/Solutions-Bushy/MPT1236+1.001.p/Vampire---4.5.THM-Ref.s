%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1236+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  51 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   47 ( 100 expanded)
%              Number of equality atoms :   17 (  40 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(global_subsumption,[],[f22,f26])).

fof(f26,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f25,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f25,plain,(
    v1_xboole_0(k1_tops_1(sK0,k1_xboole_0)) ),
    inference(global_subsumption,[],[f14,f24])).

fof(f24,plain,
    ( v1_xboole_0(k1_tops_1(sK0,k1_xboole_0))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f19,f21])).

fof(f21,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(resolution,[],[f20,f14])).

fof(f20,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_struct_0(X0) = k1_xboole_0 ) ),
    inference(resolution,[],[f17,f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

% (32181)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f17,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_struct_0(X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_struct_0(X0) = k1_xboole_0
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_struct_0(X0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_tops_1)).

fof(f14,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

fof(f22,plain,(
    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) ),
    inference(superposition,[],[f15,f21])).

fof(f15,plain,(
    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
