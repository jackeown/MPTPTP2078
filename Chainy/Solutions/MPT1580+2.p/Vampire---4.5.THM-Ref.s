%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1580+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:25 EST 2020

% Result     : Theorem 5.75s
% Output     : Refutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 129 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  201 ( 649 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7687,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7662,f3910])).

fof(f3910,plain,(
    ~ m1_subset_1(sK15,u1_struct_0(sK13)) ),
    inference(cnf_transformation,[],[f3578])).

fof(f3578,plain,
    ( ~ m1_subset_1(sK15,u1_struct_0(sK13))
    & m1_subset_1(sK15,u1_struct_0(sK14))
    & m1_yellow_0(sK14,sK13)
    & ~ v2_struct_0(sK14)
    & l1_orders_2(sK13)
    & ~ v2_struct_0(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f3080,f3577,f3576,f3575])).

fof(f3575,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,u1_struct_0(X0))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(sK13))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,sK13)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK13)
      & ~ v2_struct_0(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f3576,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(X2,u1_struct_0(sK13))
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & m1_yellow_0(X1,sK13)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK13))
          & m1_subset_1(X2,u1_struct_0(sK14)) )
      & m1_yellow_0(sK14,sK13)
      & ~ v2_struct_0(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f3577,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK13))
        & m1_subset_1(X2,u1_struct_0(sK14)) )
   => ( ~ m1_subset_1(sK15,u1_struct_0(sK13))
      & m1_subset_1(sK15,u1_struct_0(sK14)) ) ),
    introduced(choice_axiom,[])).

fof(f3080,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3079])).

fof(f3079,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3050])).

fof(f3050,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3049])).

fof(f3049,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_yellow_0)).

fof(f7662,plain,(
    m1_subset_1(sK15,u1_struct_0(sK13)) ),
    inference(resolution,[],[f7620,f3935])).

fof(f3935,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3104])).

fof(f3104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f7620,plain,(
    r2_hidden(sK15,u1_struct_0(sK13)) ),
    inference(resolution,[],[f5136,f4897])).

fof(f4897,plain,(
    r2_hidden(sK15,u1_struct_0(sK14)) ),
    inference(subsumption_resolution,[],[f4896,f3907])).

fof(f3907,plain,(
    ~ v2_struct_0(sK14) ),
    inference(cnf_transformation,[],[f3578])).

fof(f4896,plain,
    ( r2_hidden(sK15,u1_struct_0(sK14))
    | v2_struct_0(sK14) ),
    inference(subsumption_resolution,[],[f4889,f4797])).

fof(f4797,plain,(
    l1_struct_0(sK14) ),
    inference(resolution,[],[f4772,f3969])).

fof(f3969,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3124])).

fof(f3124,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1895])).

fof(f1895,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f4772,plain,(
    l1_orders_2(sK14) ),
    inference(subsumption_resolution,[],[f4769,f3906])).

fof(f3906,plain,(
    l1_orders_2(sK13) ),
    inference(cnf_transformation,[],[f3578])).

fof(f4769,plain,
    ( l1_orders_2(sK14)
    | ~ l1_orders_2(sK13) ),
    inference(resolution,[],[f3908,f3963])).

fof(f3963,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3120])).

fof(f3120,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2985])).

fof(f2985,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f3908,plain,(
    m1_yellow_0(sK14,sK13) ),
    inference(cnf_transformation,[],[f3578])).

fof(f4889,plain,
    ( r2_hidden(sK15,u1_struct_0(sK14))
    | ~ l1_struct_0(sK14)
    | v2_struct_0(sK14) ),
    inference(resolution,[],[f4789,f4648])).

fof(f4648,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3510])).

fof(f3510,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3509])).

fof(f3509,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f4789,plain,
    ( v1_xboole_0(u1_struct_0(sK14))
    | r2_hidden(sK15,u1_struct_0(sK14)) ),
    inference(resolution,[],[f3909,f3938])).

fof(f3938,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3596])).

fof(f3596,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3107])).

fof(f3107,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f3909,plain,(
    m1_subset_1(sK15,u1_struct_0(sK14)) ),
    inference(cnf_transformation,[],[f3578])).

fof(f5136,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,u1_struct_0(sK14))
      | r2_hidden(X5,u1_struct_0(sK13)) ) ),
    inference(resolution,[],[f4873,f4080])).

fof(f4080,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f3650])).

fof(f3650,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK39(X0,X1),X1)
          & r2_hidden(sK39(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK39])],[f3648,f3649])).

fof(f3649,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK39(X0,X1),X1)
        & r2_hidden(sK39(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3648,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f3647])).

fof(f3647,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3209])).

fof(f3209,plain,(
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

fof(f4873,plain,(
    r1_tarski(u1_struct_0(sK14),u1_struct_0(sK13)) ),
    inference(resolution,[],[f4770,f4772])).

fof(f4770,plain,
    ( ~ l1_orders_2(sK14)
    | r1_tarski(u1_struct_0(sK14),u1_struct_0(sK13)) ),
    inference(subsumption_resolution,[],[f4767,f3906])).

fof(f4767,plain,
    ( r1_tarski(u1_struct_0(sK14),u1_struct_0(sK13))
    | ~ l1_orders_2(sK14)
    | ~ l1_orders_2(sK13) ),
    inference(resolution,[],[f3908,f3964])).

fof(f3964,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3611])).

fof(f3611,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3610])).

fof(f3610,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3121])).

fof(f3121,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2971])).

fof(f2971,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).
%------------------------------------------------------------------------------
