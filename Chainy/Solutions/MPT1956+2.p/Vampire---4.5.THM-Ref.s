%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1956+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:38 EST 2020

% Result     : Theorem 4.26s
% Output     : Refutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 327 expanded)
%              Number of leaves         :    9 ( 107 expanded)
%              Depth                    :   11
%              Number of atoms          :  225 (2670 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7536,plain,(
    $false ),
    inference(global_subsumption,[],[f4514,f5028,f7519])).

fof(f7519,plain,(
    r3_orders_2(sK26,k1_yellow_0(sK26,sK27),k1_yellow_0(sK26,sK28)) ),
    inference(unit_resulting_resolution,[],[f4887,f4506,f4512,f4924,f4924,f5008,f4623])).

fof(f4623,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r3_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4374])).

fof(f4374,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4163])).

fof(f4163,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4162])).

fof(f4162,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1937])).

fof(f1937,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f5008,plain,(
    r1_orders_2(sK26,k1_yellow_0(sK26,sK27),k1_yellow_0(sK26,sK28)) ),
    inference(unit_resulting_resolution,[],[f4513,f4918,f4512,f4918,f4727])).

fof(f4727,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f4198])).

fof(f4198,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f4197])).

fof(f4197,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3030])).

fof(f3030,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f4918,plain,(
    ! [X8] : r1_yellow_0(sK26,X8) ),
    inference(global_subsumption,[],[f4512,f4508,f4887,f4906])).

fof(f4906,plain,(
    ! [X8] :
      ( ~ l1_orders_2(sK26)
      | r1_yellow_0(sK26,X8)
      | ~ v5_orders_2(sK26)
      | v2_struct_0(sK26) ) ),
    inference(resolution,[],[f4511,f4763])).

fof(f4763,plain,(
    ! [X0,X1] :
      ( ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4223])).

fof(f4223,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4222])).

fof(f4222,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3011])).

fof(f3011,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

fof(f4511,plain,(
    v3_lattice3(sK26) ),
    inference(cnf_transformation,[],[f4289])).

fof(f4289,plain,
    ( ( ~ r1_orders_2(sK26,k2_yellow_0(sK26,sK28),k2_yellow_0(sK26,sK27))
      | ~ r3_orders_2(sK26,k1_yellow_0(sK26,sK27),k1_yellow_0(sK26,sK28)) )
    & r1_tarski(sK27,sK28)
    & l1_orders_2(sK26)
    & v3_lattice3(sK26)
    & v2_lattice3(sK26)
    & v1_lattice3(sK26)
    & v5_orders_2(sK26)
    & v4_orders_2(sK26)
    & v3_orders_2(sK26) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26,sK27,sK28])],[f4120,f4288,f4287])).

fof(f4287,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ( ~ r1_orders_2(sK26,k2_yellow_0(sK26,X2),k2_yellow_0(sK26,X1))
            | ~ r3_orders_2(sK26,k1_yellow_0(sK26,X1),k1_yellow_0(sK26,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK26)
      & v3_lattice3(sK26)
      & v2_lattice3(sK26)
      & v1_lattice3(sK26)
      & v5_orders_2(sK26)
      & v4_orders_2(sK26)
      & v3_orders_2(sK26) ) ),
    introduced(choice_axiom,[])).

fof(f4288,plain,
    ( ? [X2,X1] :
        ( ( ~ r1_orders_2(sK26,k2_yellow_0(sK26,X2),k2_yellow_0(sK26,X1))
          | ~ r3_orders_2(sK26,k1_yellow_0(sK26,X1),k1_yellow_0(sK26,X2)) )
        & r1_tarski(X1,X2) )
   => ( ( ~ r1_orders_2(sK26,k2_yellow_0(sK26,sK28),k2_yellow_0(sK26,sK27))
        | ~ r3_orders_2(sK26,k1_yellow_0(sK26,sK27),k1_yellow_0(sK26,sK28)) )
      & r1_tarski(sK27,sK28) ) ),
    introduced(choice_axiom,[])).

fof(f4120,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f4119])).

fof(f4119,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4106])).

fof(f4106,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4105])).

fof(f4105,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).

fof(f4508,plain,(
    v5_orders_2(sK26) ),
    inference(cnf_transformation,[],[f4289])).

fof(f4513,plain,(
    r1_tarski(sK27,sK28) ),
    inference(cnf_transformation,[],[f4289])).

fof(f4924,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK26,X0),u1_struct_0(sK26)) ),
    inference(unit_resulting_resolution,[],[f4512,f4657])).

fof(f4657,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4180])).

fof(f4180,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2988])).

fof(f2988,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f4512,plain,(
    l1_orders_2(sK26) ),
    inference(cnf_transformation,[],[f4289])).

fof(f4506,plain,(
    v3_orders_2(sK26) ),
    inference(cnf_transformation,[],[f4289])).

fof(f4887,plain,(
    ~ v2_struct_0(sK26) ),
    inference(global_subsumption,[],[f4512,f4883])).

fof(f4883,plain,
    ( ~ v2_struct_0(sK26)
    | ~ l1_orders_2(sK26) ),
    inference(resolution,[],[f4509,f4811])).

fof(f4811,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4243])).

fof(f4243,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f4242])).

fof(f4242,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2806])).

fof(f2806,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f4509,plain,(
    v1_lattice3(sK26) ),
    inference(cnf_transformation,[],[f4289])).

fof(f5028,plain,(
    r1_orders_2(sK26,k2_yellow_0(sK26,sK28),k2_yellow_0(sK26,sK27)) ),
    inference(unit_resulting_resolution,[],[f4513,f4919,f4512,f4919,f4615])).

fof(f4615,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f4157])).

fof(f4157,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f4156])).

fof(f4156,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3031])).

fof(f3031,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow_0)).

fof(f4919,plain,(
    ! [X9] : r2_yellow_0(sK26,X9) ),
    inference(global_subsumption,[],[f4512,f4508,f4887,f4907])).

fof(f4907,plain,(
    ! [X9] :
      ( ~ l1_orders_2(sK26)
      | r2_yellow_0(sK26,X9)
      | ~ v5_orders_2(sK26)
      | v2_struct_0(sK26) ) ),
    inference(resolution,[],[f4511,f4764])).

fof(f4764,plain,(
    ! [X0,X1] :
      ( ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4223])).

fof(f4514,plain,
    ( ~ r1_orders_2(sK26,k2_yellow_0(sK26,sK28),k2_yellow_0(sK26,sK27))
    | ~ r3_orders_2(sK26,k1_yellow_0(sK26,sK27),k1_yellow_0(sK26,sK28)) ),
    inference(cnf_transformation,[],[f4289])).
%------------------------------------------------------------------------------
