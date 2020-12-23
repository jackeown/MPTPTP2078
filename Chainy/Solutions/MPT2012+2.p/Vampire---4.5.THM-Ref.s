%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2012+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:39 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 140 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 368 expanded)
%              Number of equality atoms :   66 ( 164 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7429,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7428,f7360])).

fof(f7360,plain,(
    k7_lattice3(sK69) != g1_orders_2(u1_struct_0(sK69),u1_orders_2(k7_lattice3(sK69))) ),
    inference(forward_demodulation,[],[f7359,f7355])).

fof(f7355,plain,(
    k7_lattice3(sK69) = g1_orders_2(u1_struct_0(sK69),u1_orders_2(k3_waybel_9(sK69))) ),
    inference(backward_demodulation,[],[f7244,f7354])).

fof(f7354,plain,(
    u1_orders_2(k3_waybel_9(sK69)) = k3_relset_1(u1_struct_0(sK69),u1_struct_0(sK69),u1_orders_2(sK69)) ),
    inference(subsumption_resolution,[],[f7353,f7189])).

fof(f7189,plain,(
    v6_waybel_0(k3_waybel_9(sK69),sK69) ),
    inference(resolution,[],[f5839,f5845])).

fof(f5845,plain,(
    ! [X0] :
      ( v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4390])).

fof(f4390,plain,(
    ! [X0] :
      ( ( l1_waybel_0(k3_waybel_9(X0),X0)
        & v6_waybel_0(k3_waybel_9(X0),X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4330])).

fof(f4330,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_waybel_0(k3_waybel_9(X0),X0)
        & v6_waybel_0(k3_waybel_9(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_9)).

fof(f5839,plain,(
    l1_orders_2(sK69) ),
    inference(cnf_transformation,[],[f5178])).

fof(f5178,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK69)),u1_orders_2(k7_lattice3(sK69))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK69)),u1_orders_2(k3_waybel_9(sK69)))
    & l1_orders_2(sK69) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK69])],[f4387,f5177])).

fof(f5177,plain,
    ( ? [X0] :
        ( g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) != g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0)))
        & l1_orders_2(X0) )
   => ( g1_orders_2(u1_struct_0(k7_lattice3(sK69)),u1_orders_2(k7_lattice3(sK69))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK69)),u1_orders_2(k3_waybel_9(sK69)))
      & l1_orders_2(sK69) ) ),
    introduced(choice_axiom,[])).

fof(f4387,plain,(
    ? [X0] :
      ( g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) != g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0)))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4361])).

fof(f4361,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0))) ) ),
    inference(negated_conjecture,[],[f4360])).

fof(f4360,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_9)).

fof(f7353,plain,
    ( u1_orders_2(k3_waybel_9(sK69)) = k3_relset_1(u1_struct_0(sK69),u1_struct_0(sK69),u1_orders_2(sK69))
    | ~ v6_waybel_0(k3_waybel_9(sK69),sK69) ),
    inference(subsumption_resolution,[],[f7315,f7190])).

fof(f7190,plain,(
    l1_waybel_0(k3_waybel_9(sK69),sK69) ),
    inference(resolution,[],[f5839,f5846])).

fof(f5846,plain,(
    ! [X0] :
      ( l1_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4390])).

fof(f7315,plain,
    ( u1_orders_2(k3_waybel_9(sK69)) = k3_relset_1(u1_struct_0(sK69),u1_struct_0(sK69),u1_orders_2(sK69))
    | ~ l1_waybel_0(k3_waybel_9(sK69),sK69)
    | ~ v6_waybel_0(k3_waybel_9(sK69),sK69) ),
    inference(resolution,[],[f5839,f7094])).

fof(f7094,plain,(
    ! [X0] :
      ( k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(k3_waybel_9(X0))
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f5842])).

fof(f5842,plain,(
    ! [X0,X1] :
      ( k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
      | k3_waybel_9(X0) != X1
      | ~ l1_waybel_0(X1,X0)
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f5180])).

fof(f5180,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k3_waybel_9(X0) = X1
              | u1_waybel_0(X0,X1) != k3_struct_0(X0)
              | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) != u1_orders_2(X1)
              | u1_struct_0(X0) != u1_struct_0(X1) )
            & ( ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
                & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
                & u1_struct_0(X0) = u1_struct_0(X1) )
              | k3_waybel_9(X0) != X1 ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f5179])).

fof(f5179,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k3_waybel_9(X0) = X1
              | u1_waybel_0(X0,X1) != k3_struct_0(X0)
              | k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) != u1_orders_2(X1)
              | u1_struct_0(X0) != u1_struct_0(X1) )
            & ( ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
                & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
                & u1_struct_0(X0) = u1_struct_0(X1) )
              | k3_waybel_9(X0) != X1 ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f4389])).

fof(f4389,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
              & u1_struct_0(X0) = u1_struct_0(X1) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f4388])).

fof(f4388,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
              & u1_struct_0(X0) = u1_struct_0(X1) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4323])).

fof(f4323,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v6_waybel_0(X1,X0) )
         => ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)) = u1_orders_2(X1)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_9)).

fof(f7244,plain,(
    k7_lattice3(sK69) = g1_orders_2(u1_struct_0(sK69),k3_relset_1(u1_struct_0(sK69),u1_struct_0(sK69),u1_orders_2(sK69))) ),
    inference(resolution,[],[f5839,f5934])).

fof(f5934,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4456])).

fof(f4456,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2827])).

fof(f2827,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

fof(f7359,plain,(
    g1_orders_2(u1_struct_0(sK69),u1_orders_2(k7_lattice3(sK69))) != g1_orders_2(u1_struct_0(sK69),u1_orders_2(k3_waybel_9(sK69))) ),
    inference(backward_demodulation,[],[f7338,f7358])).

fof(f7358,plain,(
    u1_struct_0(k3_waybel_9(sK69)) = u1_struct_0(sK69) ),
    inference(subsumption_resolution,[],[f7357,f7189])).

fof(f7357,plain,
    ( u1_struct_0(k3_waybel_9(sK69)) = u1_struct_0(sK69)
    | ~ v6_waybel_0(k3_waybel_9(sK69),sK69) ),
    inference(subsumption_resolution,[],[f7316,f7190])).

fof(f7316,plain,
    ( u1_struct_0(k3_waybel_9(sK69)) = u1_struct_0(sK69)
    | ~ l1_waybel_0(k3_waybel_9(sK69),sK69)
    | ~ v6_waybel_0(k3_waybel_9(sK69),sK69) ),
    inference(resolution,[],[f5839,f7095])).

fof(f7095,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k3_waybel_9(X0))
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f5841])).

fof(f5841,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(X1)
      | k3_waybel_9(X0) != X1
      | ~ l1_waybel_0(X1,X0)
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f5180])).

fof(f7338,plain,(
    g1_orders_2(u1_struct_0(k3_waybel_9(sK69)),u1_orders_2(k3_waybel_9(sK69))) != g1_orders_2(u1_struct_0(sK69),u1_orders_2(k7_lattice3(sK69))) ),
    inference(backward_demodulation,[],[f5840,f7240])).

fof(f7240,plain,(
    u1_struct_0(k7_lattice3(sK69)) = u1_struct_0(sK69) ),
    inference(resolution,[],[f5839,f5910])).

fof(f5910,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4439])).

fof(f4439,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4049])).

fof(f4049,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_6)).

fof(f5840,plain,(
    g1_orders_2(u1_struct_0(k7_lattice3(sK69)),u1_orders_2(k7_lattice3(sK69))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK69)),u1_orders_2(k3_waybel_9(sK69))) ),
    inference(cnf_transformation,[],[f5178])).

fof(f7428,plain,(
    k7_lattice3(sK69) = g1_orders_2(u1_struct_0(sK69),u1_orders_2(k7_lattice3(sK69))) ),
    inference(forward_demodulation,[],[f7427,f7240])).

fof(f7427,plain,(
    k7_lattice3(sK69) = g1_orders_2(u1_struct_0(k7_lattice3(sK69)),u1_orders_2(k7_lattice3(sK69))) ),
    inference(subsumption_resolution,[],[f7426,f7238])).

fof(f7238,plain,(
    l1_orders_2(k7_lattice3(sK69)) ),
    inference(resolution,[],[f5839,f5908])).

fof(f5908,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4437])).

fof(f4437,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2845])).

fof(f2845,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(f7426,plain,
    ( k7_lattice3(sK69) = g1_orders_2(u1_struct_0(k7_lattice3(sK69)),u1_orders_2(k7_lattice3(sK69)))
    | ~ l1_orders_2(k7_lattice3(sK69)) ),
    inference(resolution,[],[f7237,f5867])).

fof(f5867,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4413])).

fof(f4413,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f4412])).

fof(f4412,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1859])).

fof(f1859,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f7237,plain,(
    v1_orders_2(k7_lattice3(sK69)) ),
    inference(resolution,[],[f5839,f5907])).

fof(f5907,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4437])).
%------------------------------------------------------------------------------
