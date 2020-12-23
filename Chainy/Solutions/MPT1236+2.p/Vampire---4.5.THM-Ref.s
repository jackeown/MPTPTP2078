%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1236+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:13 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   27 (  59 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 ( 111 expanded)
%              Number of equality atoms :   12 (  37 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2816,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2815,f2697])).

fof(f2697,plain,(
    ~ v1_xboole_0(k1_tops_1(sK0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f2694,f2510])).

fof(f2510,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2222])).

fof(f2222,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f2694,plain,(
    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f2394,f2655])).

fof(f2655,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f2635,f2510])).

fof(f2635,plain,(
    v1_xboole_0(k1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f2631,f2407])).

fof(f2407,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2136])).

fof(f2136,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1797])).

fof(f1797,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

fof(f2631,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f2393,f2570])).

fof(f2570,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2279])).

fof(f2279,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2393,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2299])).

fof(f2299,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2117,f2298])).

fof(f2298,plain,
    ( ? [X0] :
        ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2117,plain,(
    ? [X0] :
      ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2116])).

fof(f2116,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f2115])).

fof(f2115,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

fof(f2394,plain,(
    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2299])).

fof(f2815,plain,(
    v1_xboole_0(k1_tops_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f2810,f2655])).

fof(f2810,plain,(
    v1_xboole_0(k1_tops_1(sK0,k1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2393,f2401])).

fof(f2401,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f2128])).

fof(f2128,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2095])).

fof(f2095,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_tops_1)).
%------------------------------------------------------------------------------
