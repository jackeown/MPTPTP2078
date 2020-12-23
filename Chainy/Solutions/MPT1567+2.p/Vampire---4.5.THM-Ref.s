%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1567+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:24 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 124 expanded)
%              Number of leaves         :    9 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  201 ( 713 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3462,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3461,f3190])).

fof(f3190,plain,(
    ~ r1_orders_2(sK0,sK1,k4_yellow_0(sK0)) ),
    inference(cnf_transformation,[],[f3120])).

fof(f3120,plain,
    ( ~ r1_orders_2(sK0,sK1,k4_yellow_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_yellow_0(sK0)
    & v5_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f3049,f3119,f3118])).

fof(f3118,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_orders_2(X0,X1,k4_yellow_0(X0))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_orders_2(sK0,X1,k4_yellow_0(sK0))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_yellow_0(sK0)
      & v5_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3119,plain,
    ( ? [X1] :
        ( ~ r1_orders_2(sK0,X1,k4_yellow_0(sK0))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ r1_orders_2(sK0,sK1,k4_yellow_0(sK0))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3049,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,k4_yellow_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3048])).

fof(f3048,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,k4_yellow_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3027])).

fof(f3027,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r1_orders_2(X0,X1,k4_yellow_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f3026])).

fof(f3026,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,k4_yellow_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_0)).

fof(f3461,plain,(
    r1_orders_2(sK0,sK1,k4_yellow_0(sK0)) ),
    inference(forward_demodulation,[],[f3452,f3350])).

fof(f3350,plain,(
    k4_yellow_0(sK0) = k2_yellow_0(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f3188,f3192])).

fof(f3192,plain,(
    ! [X0] :
      ( k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3052])).

fof(f3052,plain,(
    ! [X0] :
      ( k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2970])).

fof(f2970,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_yellow_0)).

fof(f3188,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3120])).

fof(f3452,plain,(
    r1_orders_2(sK0,sK1,k2_yellow_0(sK0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f3186,f3188,f3352,f3361,f3189,f3356,f3338])).

fof(f3338,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3205])).

fof(f3205,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X1)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3130])).

fof(f3130,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3061,f3129])).

fof(f3129,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3061,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3060])).

fof(f3060,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3034])).

fof(f3034,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f3011])).

fof(f3011,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f3356,plain,(
    ! [X0] : m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f3188,f3203])).

fof(f3203,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3059])).

fof(f3059,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2979])).

fof(f2979,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f3189,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3120])).

fof(f3361,plain,(
    r1_lattice3(sK0,k1_xboole_0,sK1) ),
    inference(unit_resulting_resolution,[],[f3188,f3189,f3337])).

fof(f3337,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3117])).

fof(f3117,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3030])).

fof(f3030,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f3352,plain,(
    r2_yellow_0(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f3185,f3186,f3187,f3188,f3196])).

fof(f3196,plain,(
    ! [X0] :
      ( r2_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3055])).

fof(f3055,plain,(
    ! [X0] :
      ( ( r1_yellow_0(X0,u1_struct_0(X0))
        & r2_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3054])).

fof(f3054,plain,(
    ! [X0] :
      ( ( r1_yellow_0(X0,u1_struct_0(X0))
        & r2_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3024])).

fof(f3024,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r1_yellow_0(X0,u1_struct_0(X0))
        & r2_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_yellow_0)).

fof(f3187,plain,(
    v2_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f3120])).

fof(f3185,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3120])).

fof(f3186,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3120])).
%------------------------------------------------------------------------------
