%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2014+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:39 EST 2020

% Result     : Theorem 2.89s
% Output     : Refutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 359 expanded)
%              Number of leaves         :   13 ( 141 expanded)
%              Depth                    :   11
%              Number of atoms          :  255 (2083 expanded)
%              Number of equality atoms :   18 (  39 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7234,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7233,f7038])).

fof(f7038,plain,(
    ~ m1_subset_1(sK18(a_3_0_waybel_9(sK14,sK15,sK16),u1_struct_0(sK15)),u1_struct_0(sK15)) ),
    inference(unit_resulting_resolution,[],[f5420,f5392,f5024])).

fof(f5024,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4481])).

fof(f4481,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f4480])).

fof(f4480,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f5392,plain,(
    ~ r2_hidden(sK18(a_3_0_waybel_9(sK14,sK15,sK16),u1_struct_0(sK15)),u1_struct_0(sK15)) ),
    inference(unit_resulting_resolution,[],[f5382,f4890])).

fof(f4890,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK18(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f4669])).

fof(f4669,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK18(X0,X1),X1)
          & r2_hidden(sK18(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f4667,f4668])).

fof(f4668,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK18(X0,X1),X1)
        & r2_hidden(sK18(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f4667,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f4666])).

fof(f4666,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4398])).

fof(f4398,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f5382,plain,(
    ~ r1_tarski(a_3_0_waybel_9(sK14,sK15,sK16),u1_struct_0(sK15)) ),
    inference(backward_demodulation,[],[f4864,f5380])).

fof(f5380,plain,(
    u1_struct_0(k4_waybel_9(sK14,sK15,sK16)) = a_3_0_waybel_9(sK14,sK15,sK16) ),
    inference(unit_resulting_resolution,[],[f4859,f4860,f4861,f4862,f4863,f4925])).

fof(f4925,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4416])).

fof(f4416,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4415])).

fof(f4415,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4364])).

fof(f4364,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_9)).

fof(f4863,plain,(
    m1_subset_1(sK16,u1_struct_0(sK15)) ),
    inference(cnf_transformation,[],[f4660])).

fof(f4660,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK14,sK15,sK16)),u1_struct_0(sK15))
    & m1_subset_1(sK16,u1_struct_0(sK15))
    & l1_waybel_0(sK15,sK14)
    & ~ v2_struct_0(sK15)
    & l1_struct_0(sK14)
    & ~ v2_struct_0(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f4382,f4659,f4658,f4657])).

fof(f4657,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK14,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK14)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK14)
      & ~ v2_struct_0(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f4658,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK14,X1,X2)),u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_waybel_0(X1,sK14)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK14,sK15,X2)),u1_struct_0(sK15))
          & m1_subset_1(X2,u1_struct_0(sK15)) )
      & l1_waybel_0(sK15,sK14)
      & ~ v2_struct_0(sK15) ) ),
    introduced(choice_axiom,[])).

fof(f4659,plain,
    ( ? [X2] :
        ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK14,sK15,X2)),u1_struct_0(sK15))
        & m1_subset_1(X2,u1_struct_0(sK15)) )
   => ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK14,sK15,sK16)),u1_struct_0(sK15))
      & m1_subset_1(sK16,u1_struct_0(sK15)) ) ),
    introduced(choice_axiom,[])).

fof(f4382,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4381])).

fof(f4381,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4366])).

fof(f4366,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f4365])).

fof(f4365,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

fof(f4862,plain,(
    l1_waybel_0(sK15,sK14) ),
    inference(cnf_transformation,[],[f4660])).

fof(f4861,plain,(
    ~ v2_struct_0(sK15) ),
    inference(cnf_transformation,[],[f4660])).

fof(f4860,plain,(
    l1_struct_0(sK14) ),
    inference(cnf_transformation,[],[f4660])).

fof(f4859,plain,(
    ~ v2_struct_0(sK14) ),
    inference(cnf_transformation,[],[f4660])).

fof(f4864,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9(sK14,sK15,sK16)),u1_struct_0(sK15)) ),
    inference(cnf_transformation,[],[f4660])).

fof(f5420,plain,(
    ~ v1_xboole_0(u1_struct_0(sK15)) ),
    inference(unit_resulting_resolution,[],[f4861,f5357,f4938])).

fof(f4938,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4694])).

fof(f4694,plain,(
    ! [X0] :
      ( ( ( v2_struct_0(X0)
          | ~ v1_xboole_0(u1_struct_0(X0)) )
        & ( v1_xboole_0(u1_struct_0(X0))
          | ~ v2_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4428])).

fof(f4428,plain,(
    ! [X0] :
      ( ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3837])).

fof(f3837,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_struct_0)).

fof(f5357,plain,(
    l1_struct_0(sK15) ),
    inference(unit_resulting_resolution,[],[f5348,f4935])).

fof(f4935,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4426])).

fof(f4426,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1895])).

fof(f1895,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f5348,plain,(
    l1_orders_2(sK15) ),
    inference(unit_resulting_resolution,[],[f4860,f4862,f4928])).

fof(f4928,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4418])).

fof(f4418,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3197])).

fof(f3197,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f7233,plain,(
    m1_subset_1(sK18(a_3_0_waybel_9(sK14,sK15,sK16),u1_struct_0(sK15)),u1_struct_0(sK15)) ),
    inference(forward_demodulation,[],[f7211,f7212])).

fof(f7212,plain,(
    sK18(a_3_0_waybel_9(sK14,sK15,sK16),u1_struct_0(sK15)) = sK90(sK18(a_3_0_waybel_9(sK14,sK15,sK16),u1_struct_0(sK15)),sK15,sK16) ),
    inference(unit_resulting_resolution,[],[f4859,f4860,f4861,f4862,f4863,f5391,f5275])).

fof(f5275,plain,(
    ! [X2,X0,X3,X1] :
      ( sK90(X0,X2,X3) = X0
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f4856])).

fof(f4856,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ( r1_orders_2(X2,X3,sK90(X0,X2,X3))
            & sK90(X0,X2,X3) = X0
            & m1_subset_1(sK90(X0,X2,X3),u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK90])],[f4854,f4855])).

fof(f4855,plain,(
    ! [X3,X2,X0] :
      ( ? [X5] :
          ( r1_orders_2(X2,X3,X5)
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( r1_orders_2(X2,X3,sK90(X0,X2,X3))
        & sK90(X0,X2,X3) = X0
        & m1_subset_1(sK90(X0,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4854,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X5] :
              ( r1_orders_2(X2,X3,X5)
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f4853])).

fof(f4853,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X4] :
              ( r1_orders_2(X2,X3,X4)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f4635])).

fof(f4635,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f4634])).

fof(f4634,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4357])).

fof(f4357,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X2))
        & l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

fof(f5391,plain,(
    r2_hidden(sK18(a_3_0_waybel_9(sK14,sK15,sK16),u1_struct_0(sK15)),a_3_0_waybel_9(sK14,sK15,sK16)) ),
    inference(unit_resulting_resolution,[],[f5382,f4889])).

fof(f4889,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK18(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f4669])).

fof(f7211,plain,(
    m1_subset_1(sK90(sK18(a_3_0_waybel_9(sK14,sK15,sK16),u1_struct_0(sK15)),sK15,sK16),u1_struct_0(sK15)) ),
    inference(unit_resulting_resolution,[],[f4859,f4860,f4861,f4862,f4863,f5391,f5274])).

fof(f5274,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK90(X0,X2,X3),u1_struct_0(X2))
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f4856])).
%------------------------------------------------------------------------------
