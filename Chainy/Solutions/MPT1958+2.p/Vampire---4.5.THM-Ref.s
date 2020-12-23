%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1958+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:38 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  106 (1104 expanded)
%              Number of leaves         :   12 ( 246 expanded)
%              Depth                    :   34
%              Number of atoms          :  382 (6488 expanded)
%              Number of equality atoms :   49 (1343 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9589,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9588,f4359])).

fof(f4359,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f4287])).

fof(f4287,plain,
    ( ( k3_yellow_0(sK0) != k4_yellow_0(sK0)
      | ~ v7_struct_0(sK0) )
    & ( k3_yellow_0(sK0) = k4_yellow_0(sK0)
      | v7_struct_0(sK0) )
    & l1_orders_2(sK0)
    & v3_yellow_0(sK0)
    & v5_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4285,f4286])).

fof(f4286,plain,
    ( ? [X0] :
        ( ( k3_yellow_0(X0) != k4_yellow_0(X0)
          | ~ v7_struct_0(X0) )
        & ( k3_yellow_0(X0) = k4_yellow_0(X0)
          | v7_struct_0(X0) )
        & l1_orders_2(X0)
        & v3_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k3_yellow_0(sK0) != k4_yellow_0(sK0)
        | ~ v7_struct_0(sK0) )
      & ( k3_yellow_0(sK0) = k4_yellow_0(sK0)
        | v7_struct_0(sK0) )
      & l1_orders_2(sK0)
      & v3_yellow_0(sK0)
      & v5_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f4285,plain,(
    ? [X0] :
      ( ( k3_yellow_0(X0) != k4_yellow_0(X0)
        | ~ v7_struct_0(X0) )
      & ( k3_yellow_0(X0) = k4_yellow_0(X0)
        | v7_struct_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4284])).

fof(f4284,plain,(
    ? [X0] :
      ( ( k3_yellow_0(X0) != k4_yellow_0(X0)
        | ~ v7_struct_0(X0) )
      & ( k3_yellow_0(X0) = k4_yellow_0(X0)
        | v7_struct_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4121])).

fof(f4121,plain,(
    ? [X0] :
      ( ( v7_struct_0(X0)
      <~> k3_yellow_0(X0) = k4_yellow_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4120])).

fof(f4120,plain,(
    ? [X0] :
      ( ( v7_struct_0(X0)
      <~> k3_yellow_0(X0) = k4_yellow_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4119])).

fof(f4119,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v7_struct_0(X0)
        <=> k3_yellow_0(X0) = k4_yellow_0(X0) ) ) ),
    inference(negated_conjecture,[],[f4118])).

fof(f4118,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> k3_yellow_0(X0) = k4_yellow_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_waybel_7)).

fof(f9588,plain,(
    ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f9587,f4361])).

fof(f4361,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f4287])).

fof(f9587,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f9586,f4778])).

fof(f4778,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f4361,f4417])).

fof(f4417,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4161])).

fof(f4161,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2990])).

fof(f2990,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f9586,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f9585,f9028])).

fof(f9028,plain,(
    m1_subset_1(sK26(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f8945,f4783])).

fof(f4783,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f4361,f4591])).

fof(f4591,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4266])).

fof(f4266,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1895])).

fof(f1895,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f8945,plain,
    ( m1_subset_1(sK26(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f8876,f4583])).

fof(f4583,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | m1_subset_1(sK26(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4353])).

fof(f4353,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ( sK25(X0) != sK26(X0)
            & m1_subset_1(sK26(X0),u1_struct_0(X0))
            & m1_subset_1(sK25(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25,sK26])],[f4350,f4352,f4351])).

fof(f4351,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK25(X0) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK25(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4352,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK25(X0) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK25(X0) != sK26(X0)
        & m1_subset_1(sK26(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4350,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(rectify,[],[f4349])).

fof(f4349,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( X1 = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4255])).

fof(f4255,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4111])).

fof(f4111,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v7_struct_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_struct_0)).

fof(f8876,plain,(
    ~ v7_struct_0(sK0) ),
    inference(trivial_inequality_removal,[],[f8857])).

fof(f8857,plain,
    ( k3_yellow_0(sK0) != k3_yellow_0(sK0)
    | ~ v7_struct_0(sK0) ),
    inference(backward_demodulation,[],[f4363,f8845])).

fof(f8845,plain,(
    k3_yellow_0(sK0) = k4_yellow_0(sK0) ),
    inference(subsumption_resolution,[],[f8824,f4362])).

fof(f4362,plain,
    ( v7_struct_0(sK0)
    | k3_yellow_0(sK0) = k4_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f4287])).

fof(f8824,plain,
    ( k3_yellow_0(sK0) = k4_yellow_0(sK0)
    | ~ v7_struct_0(sK0) ),
    inference(resolution,[],[f5311,f4778])).

fof(f5311,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_yellow_0(sK0) = X0
      | ~ v7_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f5290,f4783])).

fof(f5290,plain,(
    ! [X0] :
      ( k4_yellow_0(sK0) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_struct_0(sK0)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f4775,f4581])).

fof(f4581,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4353])).

fof(f4775,plain,(
    m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f4361,f4411])).

fof(f4411,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4153])).

fof(f4153,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2991])).

fof(f2991,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_0)).

fof(f4363,plain,
    ( k3_yellow_0(sK0) != k4_yellow_0(sK0)
    | ~ v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f4287])).

fof(f9585,plain,
    ( ~ m1_subset_1(sK26(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f9584,f9313])).

fof(f9313,plain,(
    r1_orders_2(sK0,sK26(sK0),k3_yellow_0(sK0)) ),
    inference(forward_demodulation,[],[f9312,f8845])).

fof(f9312,plain,(
    r1_orders_2(sK0,sK26(sK0),k4_yellow_0(sK0)) ),
    inference(subsumption_resolution,[],[f9311,f4358])).

fof(f4358,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f4287])).

fof(f9311,plain,
    ( r1_orders_2(sK0,sK26(sK0),k4_yellow_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f9310,f4359])).

fof(f9310,plain,
    ( r1_orders_2(sK0,sK26(sK0),k4_yellow_0(sK0))
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f9309,f4816])).

fof(f4816,plain,(
    v2_yellow_0(sK0) ),
    inference(subsumption_resolution,[],[f4796,f4360])).

fof(f4360,plain,(
    v3_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f4287])).

fof(f4796,plain,
    ( v2_yellow_0(sK0)
    | ~ v3_yellow_0(sK0) ),
    inference(resolution,[],[f4361,f4608])).

fof(f4608,plain,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4277])).

fof(f4277,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f4276])).

fof(f4276,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2968])).

fof(f2968,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_yellow_0(X0)
       => ( v2_yellow_0(X0)
          & v1_yellow_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_0)).

fof(f9309,plain,
    ( r1_orders_2(sK0,sK26(sK0),k4_yellow_0(sK0))
    | ~ v2_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f9297,f4361])).

fof(f9297,plain,
    ( r1_orders_2(sK0,sK26(sK0),k4_yellow_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f9028,f4409])).

fof(f4409,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,k4_yellow_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4151])).

fof(f4151,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4150])).

fof(f4150,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3042])).

fof(f3042,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,k4_yellow_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_0)).

fof(f9584,plain,
    ( ~ r1_orders_2(sK0,sK26(sK0),k3_yellow_0(sK0))
    | ~ m1_subset_1(sK26(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f9582,f9565])).

fof(f9565,plain,(
    k3_yellow_0(sK0) != sK26(sK0) ),
    inference(backward_demodulation,[],[f9029,f9552])).

fof(f9552,plain,(
    k3_yellow_0(sK0) = sK25(sK0) ),
    inference(subsumption_resolution,[],[f9551,f4359])).

fof(f9551,plain,
    ( k3_yellow_0(sK0) = sK25(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f9550,f4361])).

fof(f9550,plain,
    ( k3_yellow_0(sK0) = sK25(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f9549,f4778])).

fof(f9549,plain,
    ( k3_yellow_0(sK0) = sK25(sK0)
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f9548,f9027])).

fof(f9027,plain,(
    m1_subset_1(sK25(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f8944,f4783])).

fof(f8944,plain,
    ( m1_subset_1(sK25(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f8876,f4582])).

fof(f4582,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | m1_subset_1(sK25(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4353])).

fof(f9548,plain,
    ( k3_yellow_0(sK0) = sK25(sK0)
    | ~ m1_subset_1(sK25(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f9546,f9279])).

fof(f9279,plain,(
    r1_orders_2(sK0,sK25(sK0),k3_yellow_0(sK0)) ),
    inference(forward_demodulation,[],[f9278,f8845])).

fof(f9278,plain,(
    r1_orders_2(sK0,sK25(sK0),k4_yellow_0(sK0)) ),
    inference(subsumption_resolution,[],[f9277,f4358])).

fof(f9277,plain,
    ( r1_orders_2(sK0,sK25(sK0),k4_yellow_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f9276,f4359])).

fof(f9276,plain,
    ( r1_orders_2(sK0,sK25(sK0),k4_yellow_0(sK0))
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f9275,f4816])).

fof(f9275,plain,
    ( r1_orders_2(sK0,sK25(sK0),k4_yellow_0(sK0))
    | ~ v2_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f9263,f4361])).

fof(f9263,plain,
    ( r1_orders_2(sK0,sK25(sK0),k4_yellow_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f9027,f4409])).

fof(f9546,plain,
    ( k3_yellow_0(sK0) = sK25(sK0)
    | ~ r1_orders_2(sK0,sK25(sK0),k3_yellow_0(sK0))
    | ~ m1_subset_1(sK25(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f9283,f4609])).

fof(f4609,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4279])).

fof(f4279,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f4278])).

fof(f4278,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1953])).

fof(f1953,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f9283,plain,(
    r1_orders_2(sK0,k3_yellow_0(sK0),sK25(sK0)) ),
    inference(subsumption_resolution,[],[f9282,f4358])).

fof(f9282,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK25(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f9281,f4359])).

fof(f9281,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK25(sK0))
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f9280,f4815])).

fof(f4815,plain,(
    v1_yellow_0(sK0) ),
    inference(subsumption_resolution,[],[f4795,f4360])).

fof(f4795,plain,
    ( v1_yellow_0(sK0)
    | ~ v3_yellow_0(sK0) ),
    inference(resolution,[],[f4361,f4607])).

fof(f4607,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4277])).

fof(f9280,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK25(sK0))
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f9264,f4361])).

fof(f9264,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK25(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f9027,f4415])).

fof(f4415,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4159])).

fof(f4159,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4158])).

fof(f4158,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3041])).

fof(f3041,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f9029,plain,(
    sK25(sK0) != sK26(sK0) ),
    inference(subsumption_resolution,[],[f8946,f4783])).

fof(f8946,plain,
    ( sK25(sK0) != sK26(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f8876,f4584])).

fof(f4584,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | sK25(X0) != sK26(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4353])).

fof(f9582,plain,
    ( k3_yellow_0(sK0) = sK26(sK0)
    | ~ r1_orders_2(sK0,sK26(sK0),k3_yellow_0(sK0))
    | ~ m1_subset_1(sK26(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f9317,f4609])).

fof(f9317,plain,(
    r1_orders_2(sK0,k3_yellow_0(sK0),sK26(sK0)) ),
    inference(subsumption_resolution,[],[f9316,f4358])).

fof(f9316,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK26(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f9315,f4359])).

fof(f9315,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK26(sK0))
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f9314,f4815])).

fof(f9314,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK26(sK0))
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f9298,f4361])).

fof(f9298,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK26(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f9028,f4415])).
%------------------------------------------------------------------------------
