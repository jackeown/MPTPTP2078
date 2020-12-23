%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1918+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 303 expanded)
%              Number of leaves         :    7 ( 117 expanded)
%              Depth                    :   10
%              Number of atoms          :  144 (1210 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4203,plain,(
    $false ),
    inference(global_subsumption,[],[f4021,f4131,f4201])).

fof(f4201,plain,(
    r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f4053,f4094])).

fof(f4094,plain,(
    r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) ),
    inference(subsumption_resolution,[],[f4004,f4005])).

fof(f4005,plain,(
    l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f4001,f3985])).

fof(f3985,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3981,f3921])).

fof(f3921,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3896])).

fof(f3896,plain,
    ( ~ m1_yellow_0(sK2,sK0)
    & m1_yellow_0(sK2,sK1)
    & m1_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3869,f3895,f3894,f3893])).

fof(f3893,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_yellow_0(X2,X0)
                & m1_yellow_0(X2,X1) )
            & m1_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow_0(X2,sK0)
              & m1_yellow_0(X2,X1) )
          & m1_yellow_0(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3894,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_yellow_0(X2,sK0)
            & m1_yellow_0(X2,X1) )
        & m1_yellow_0(X1,sK0) )
   => ( ? [X2] :
          ( ~ m1_yellow_0(X2,sK0)
          & m1_yellow_0(X2,sK1) )
      & m1_yellow_0(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3895,plain,
    ( ? [X2] :
        ( ~ m1_yellow_0(X2,sK0)
        & m1_yellow_0(X2,sK1) )
   => ( ~ m1_yellow_0(sK2,sK0)
      & m1_yellow_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3869,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow_0(X2,X0)
              & m1_yellow_0(X2,X1) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3857])).

fof(f3857,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_yellow_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_0(X2,X1)
               => m1_yellow_0(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f3856])).

fof(f3856,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_0(X2,X1)
             => m1_yellow_0(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_6)).

fof(f3981,plain,
    ( l1_orders_2(sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3922,f3927])).

fof(f3927,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3873])).

fof(f3873,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2992])).

fof(f2992,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f3922,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3896])).

fof(f4001,plain,
    ( l1_orders_2(sK2)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f3923,f3927])).

fof(f3923,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f3896])).

fof(f4004,plain,
    ( r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f4000,f3985])).

fof(f4000,plain,
    ( r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))
    | ~ l1_orders_2(sK2)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f3923,f3929])).

fof(f3929,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3900])).

fof(f3900,plain,(
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
    inference(flattening,[],[f3899])).

fof(f3899,plain,(
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
    inference(nnf_transformation,[],[f3874])).

fof(f3874,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2976])).

fof(f2976,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

fof(f4053,plain,(
    ! [X10] :
      ( ~ r1_tarski(X10,u1_orders_2(sK1))
      | r1_tarski(X10,u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f4046,f3939])).

fof(f3939,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3884])).

fof(f3884,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f3883])).

fof(f3883,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f4046,plain,(
    r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f3984,f3985])).

fof(f3984,plain,
    ( r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3980,f3921])).

fof(f3980,plain,
    ( r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3922,f3929])).

fof(f4131,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f4029,f4065])).

fof(f4065,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f4003,f4005])).

fof(f4003,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f3999,f3985])).

fof(f3999,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK2)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f3923,f3928])).

fof(f3928,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3900])).

fof(f4029,plain,(
    ! [X10] :
      ( ~ r1_tarski(X10,u1_struct_0(sK1))
      | r1_tarski(X10,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f4022,f3939])).

fof(f4022,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f3983,f3985])).

fof(f3983,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3979,f3921])).

fof(f3979,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3922,f3928])).

fof(f4021,plain,
    ( ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4020,f3921])).

fof(f4020,plain,
    ( ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f4019,f4005])).

fof(f4019,plain,
    ( ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK2)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3924,f3930])).

fof(f3930,plain,(
    ! [X0,X1] :
      ( m1_yellow_0(X1,X0)
      | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3900])).

fof(f3924,plain,(
    ~ m1_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f3896])).
%------------------------------------------------------------------------------
