%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1566+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:24 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 133 expanded)
%              Number of leaves         :    9 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  232 ( 744 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4012,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4011,f3177])).

fof(f3177,plain,(
    ~ r1_orders_2(sK4,k3_yellow_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f3110])).

fof(f3110,plain,
    ( ~ r1_orders_2(sK4,k3_yellow_0(sK4),sK5)
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v1_yellow_0(sK4)
    & v5_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f3043,f3109,f3108])).

fof(f3108,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_orders_2(X0,k3_yellow_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_orders_2(sK4,k3_yellow_0(sK4),X1)
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v1_yellow_0(sK4)
      & v5_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3109,plain,
    ( ? [X1] :
        ( ~ r1_orders_2(sK4,k3_yellow_0(sK4),X1)
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( ~ r1_orders_2(sK4,k3_yellow_0(sK4),sK5)
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f3043,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,k3_yellow_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3042])).

fof(f3042,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,k3_yellow_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3024])).

fof(f3024,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f3023])).

fof(f3023,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f4011,plain,(
    r1_orders_2(sK4,k3_yellow_0(sK4),sK5) ),
    inference(forward_demodulation,[],[f4010,f3452])).

fof(f3452,plain,(
    k3_yellow_0(sK4) = k1_yellow_0(sK4,k1_xboole_0) ),
    inference(resolution,[],[f3175,f3179])).

fof(f3179,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3046])).

fof(f3046,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2969])).

fof(f2969,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f3175,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f3110])).

fof(f4010,plain,(
    r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),sK5) ),
    inference(subsumption_resolution,[],[f4009,f3173])).

fof(f3173,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f3110])).

fof(f4009,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),sK5)
    | ~ v5_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f4008,f3175])).

fof(f4008,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),sK5)
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f4007,f3459])).

fof(f3459,plain,(
    ! [X3] : m1_subset_1(k1_yellow_0(sK4,X3),u1_struct_0(sK4)) ),
    inference(resolution,[],[f3175,f3188])).

fof(f3188,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3051])).

fof(f3051,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2977])).

fof(f2977,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f4007,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),sK5)
    | ~ m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f4006,f3337])).

fof(f3337,plain,(
    r1_yellow_0(sK4,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f3336,f3173])).

fof(f3336,plain,
    ( r1_yellow_0(sK4,k1_xboole_0)
    | ~ v5_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f3335,f3174])).

fof(f3174,plain,(
    v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f3110])).

fof(f3335,plain,
    ( r1_yellow_0(sK4,k1_xboole_0)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f3329,f3175])).

fof(f3329,plain,
    ( r1_yellow_0(sK4,k1_xboole_0)
    | ~ l1_orders_2(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ v5_orders_2(sK4) ),
    inference(resolution,[],[f3172,f3183])).

fof(f3183,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3049])).

fof(f3049,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3048])).

fof(f3048,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3021])).

fof(f3021,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f3172,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f3110])).

fof(f4006,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),sK5)
    | ~ r1_yellow_0(sK4,k1_xboole_0)
    | ~ m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f3917,f3176])).

fof(f3176,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f3110])).

fof(f3917,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r1_yellow_0(sK4,k1_xboole_0)
    | ~ m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4) ),
    inference(resolution,[],[f3728,f3317])).

fof(f3317,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X2),X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3190])).

fof(f3190,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X1,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3120])).

fof(f3120,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK9(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK9(X0,X1,X2))
                  & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f3053,f3119])).

fof(f3119,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK9(X0,X1,X2))
        & r2_lattice3(X0,X2,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3053,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3052])).

fof(f3052,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3031])).

fof(f3031,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f3008])).

fof(f3008,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f3728,plain,(
    r2_lattice3(sK4,k1_xboole_0,sK5) ),
    inference(subsumption_resolution,[],[f3638,f3175])).

fof(f3638,plain,
    ( r2_lattice3(sK4,k1_xboole_0,sK5)
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f3176,f3313])).

fof(f3313,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3099])).

fof(f3099,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3027])).

fof(f3027,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).
%------------------------------------------------------------------------------
