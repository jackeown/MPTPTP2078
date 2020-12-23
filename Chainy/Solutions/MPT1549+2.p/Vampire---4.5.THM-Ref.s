%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1549+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:24 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  123 (1636 expanded)
%              Number of leaves         :   12 ( 556 expanded)
%              Depth                    :   29
%              Number of atoms          :  618 (7802 expanded)
%              Number of equality atoms :  127 (3046 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3840,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3839,f3053])).

fof(f3053,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3036])).

fof(f3036,plain,
    ( k2_yellow_0(sK2,sK4) != k2_yellow_0(sK3,sK4)
    & r2_yellow_0(sK2,sK4)
    & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    & l1_orders_2(sK3)
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f3015,f3035,f3034,f3033])).

fof(f3033,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                & r2_yellow_0(X0,X2) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X1,X2) != k2_yellow_0(sK2,X2)
              & r2_yellow_0(sK2,X2) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
          & l1_orders_2(X1) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3034,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_yellow_0(X1,X2) != k2_yellow_0(sK2,X2)
            & r2_yellow_0(sK2,X2) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( k2_yellow_0(sK2,X2) != k2_yellow_0(sK3,X2)
          & r2_yellow_0(sK2,X2) )
      & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      & l1_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3035,plain,
    ( ? [X2] :
        ( k2_yellow_0(sK2,X2) != k2_yellow_0(sK3,X2)
        & r2_yellow_0(sK2,X2) )
   => ( k2_yellow_0(sK2,sK4) != k2_yellow_0(sK3,sK4)
      & r2_yellow_0(sK2,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3015,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f3014])).

fof(f3014,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2997])).

fof(f2997,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( r2_yellow_0(X0,X2)
                 => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f2996])).

fof(f2996,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r2_yellow_0(X0,X2)
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_0)).

fof(f3839,plain,(
    ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f3829,f3058])).

fof(f3058,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3016,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2975])).

fof(f2975,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f3829,plain,(
    ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f3828,f3810])).

fof(f3810,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5(sK3,sK4,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f3794,f3809])).

fof(f3809,plain,
    ( r1_lattice3(sK2,sK4,sK5(sK3,sK4,k2_yellow_0(sK2,sK4)))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f3802,f3057])).

fof(f3057,plain,(
    k2_yellow_0(sK2,sK4) != k2_yellow_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f3036])).

fof(f3802,plain,
    ( k2_yellow_0(sK2,sK4) = k2_yellow_0(sK3,sK4)
    | r1_lattice3(sK2,sK4,sK5(sK3,sK4,k2_yellow_0(sK2,sK4)))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(resolution,[],[f3460,f3459])).

fof(f3459,plain,(
    r1_lattice3(sK3,sK4,k2_yellow_0(sK2,sK4)) ),
    inference(resolution,[],[f3444,f3056])).

fof(f3056,plain,(
    r2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f3036])).

fof(f3444,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | r1_lattice3(sK3,X0,k2_yellow_0(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f3443,f3053])).

fof(f3443,plain,(
    ! [X0] :
      ( r1_lattice3(sK3,X0,k2_yellow_0(sK2,X0))
      | ~ r2_yellow_0(sK2,X0)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f3384,f3106])).

fof(f3106,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f3098,f3058])).

fof(f3098,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3059])).

fof(f3059,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3041,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK5(X0,X1,X2))
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3039,f3040])).

fof(f3040,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3039,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3038])).

fof(f3038,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3037])).

fof(f3037,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3018])).

fof(f3018,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3017])).

fof(f3017,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2968])).

fof(f2968,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f3384,plain,(
    ! [X4,X5] :
      ( ~ r1_lattice3(sK2,X4,k2_yellow_0(sK2,X5))
      | r1_lattice3(sK3,X4,k2_yellow_0(sK2,X5)) ) ),
    inference(subsumption_resolution,[],[f3379,f3053])).

fof(f3379,plain,(
    ! [X4,X5] :
      ( ~ r1_lattice3(sK2,X4,k2_yellow_0(sK2,X5))
      | r1_lattice3(sK3,X4,k2_yellow_0(sK2,X5))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f3260,f3058])).

fof(f3260,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X1,X0)
      | r1_lattice3(sK3,X1,X0) ) ),
    inference(trivial_inequality_removal,[],[f3259])).

fof(f3259,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X1,X0)
      | r1_lattice3(sK3,X1,X0) ) ),
    inference(forward_demodulation,[],[f3258,f3147])).

fof(f3147,plain,(
    u1_orders_2(sK2) = u1_orders_2(sK3) ),
    inference(equality_resolution,[],[f3141])).

fof(f3141,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | u1_orders_2(sK3) = X1 ) ),
    inference(superposition,[],[f3131,f3118])).

fof(f3118,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3)) ),
    inference(backward_demodulation,[],[f3055,f3116])).

fof(f3116,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(trivial_inequality_removal,[],[f3114])).

fof(f3114,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(superposition,[],[f3110,f3055])).

fof(f3110,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | u1_struct_0(sK2) = X0 ) ),
    inference(resolution,[],[f3109,f3053])).

fof(f3109,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) ),
    inference(resolution,[],[f3087,f3095])).

fof(f3095,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3029])).

fof(f3029,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f3087,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f3023])).

fof(f3023,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f1926])).

fof(f1926,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f3055,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f3036])).

fof(f3131,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
      | u1_orders_2(sK3) = X1 ) ),
    inference(resolution,[],[f3124,f3088])).

fof(f3088,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f3023])).

fof(f3124,plain,(
    m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f3121,f3054])).

fof(f3054,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f3036])).

fof(f3121,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ l1_orders_2(sK3) ),
    inference(superposition,[],[f3095,f3116])).

fof(f3258,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X1,X0)
      | r1_lattice3(sK3,X1,X0) ) ),
    inference(subsumption_resolution,[],[f3257,f3054])).

fof(f3257,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X1,X0)
      | ~ l1_orders_2(sK3)
      | r1_lattice3(sK3,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f3253])).

fof(f3253,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X1,X0)
      | ~ l1_orders_2(sK3)
      | r1_lattice3(sK3,X1,X0) ) ),
    inference(superposition,[],[f3190,f3116])).

fof(f3190,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X0,X1)
      | ~ l1_orders_2(X2)
      | r1_lattice3(X2,X0,X1) ) ),
    inference(resolution,[],[f3099,f3053])).

fof(f3099,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | r1_lattice3(X1,X2,X4) ) ),
    inference(equality_resolution,[],[f3090])).

fof(f3090,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_lattice3(X1,X2,X4)
      | ~ r1_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3025])).

fof(f3025,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3024])).

fof(f3024,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2998])).

fof(f2998,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_0)).

fof(f3460,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK3,sK4,X0)
      | k2_yellow_0(sK3,sK4) = X0
      | r1_lattice3(sK2,sK4,sK5(sK3,sK4,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f3281,f3238])).

fof(f3238,plain,(
    r2_yellow_0(sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f3237])).

fof(f3237,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | r2_yellow_0(sK3,sK4) ),
    inference(forward_demodulation,[],[f3236,f3147])).

fof(f3236,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
    | r2_yellow_0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f3233,f3054])).

fof(f3233,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
    | r2_yellow_0(sK3,sK4)
    | ~ l1_orders_2(sK3) ),
    inference(superposition,[],[f3129,f3116])).

fof(f3129,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | r2_yellow_0(X0,sK4)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f3128,f3053])).

fof(f3128,plain,(
    ! [X0] :
      ( r2_yellow_0(X0,sK4)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f3086,f3056])).

fof(f3086,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X2)
      | r2_yellow_0(X1,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3022])).

fof(f3022,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X0,X2) )
              & ( r1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X0,X2) ) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3021])).

fof(f3021,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X0,X2) )
              & ( r1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X0,X2) ) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2982])).

fof(f2982,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( r2_yellow_0(X0,X2)
                 => r2_yellow_0(X1,X2) )
                & ( r1_yellow_0(X0,X2)
                 => r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_0)).

fof(f3281,plain,(
    ! [X2,X1] :
      ( ~ r2_yellow_0(sK3,X1)
      | r1_lattice3(sK2,X1,sK5(sK3,X1,X2))
      | k2_yellow_0(sK3,X1) = X2
      | ~ r1_lattice3(sK3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f3280,f3139])).

fof(f3139,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK3,X0)
      | k2_yellow_0(sK3,X0) = X1
      | ~ r1_lattice3(sK3,X0,X1)
      | m1_subset_1(sK5(sK3,X0,X1),u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f3138,f3054])).

fof(f3138,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(sK3,X0,X1),u1_struct_0(sK2))
      | k2_yellow_0(sK3,X0) = X1
      | ~ r1_lattice3(sK3,X0,X1)
      | ~ r2_yellow_0(sK3,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ l1_orders_2(sK3) ) ),
    inference(superposition,[],[f3061,f3116])).

fof(f3061,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3280,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5(sK3,X1,X2),u1_struct_0(sK2))
      | r1_lattice3(sK2,X1,sK5(sK3,X1,X2))
      | k2_yellow_0(sK3,X1) = X2
      | ~ r1_lattice3(sK3,X1,X2)
      | ~ r2_yellow_0(sK3,X1) ) ),
    inference(forward_demodulation,[],[f3279,f3116])).

fof(f3279,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK5(sK3,X1,X2),u1_struct_0(sK2))
      | r1_lattice3(sK2,X1,sK5(sK3,X1,X2))
      | k2_yellow_0(sK3,X1) = X2
      | ~ r1_lattice3(sK3,X1,X2)
      | ~ r2_yellow_0(sK3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f3273,f3054])).

fof(f3273,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK5(sK3,X1,X2),u1_struct_0(sK2))
      | r1_lattice3(sK2,X1,sK5(sK3,X1,X2))
      | k2_yellow_0(sK3,X1) = X2
      | ~ r1_lattice3(sK3,X1,X2)
      | ~ r2_yellow_0(sK3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ l1_orders_2(sK3) ) ),
    inference(resolution,[],[f3269,f3062])).

fof(f3062,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3269,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK3,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_lattice3(sK2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f3267,f3053])).

fof(f3267,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK3,X1,X0)
      | ~ l1_orders_2(sK2)
      | r1_lattice3(sK2,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f3266])).

fof(f3266,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK3,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | r1_lattice3(sK2,X1,X0) ) ),
    inference(equality_resolution,[],[f3195])).

fof(f3195,plain,(
    ! [X4,X5,X3] :
      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X5),u1_orders_2(X5))
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r1_lattice3(sK3,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | r1_lattice3(X5,X3,X4) ) ),
    inference(forward_demodulation,[],[f3194,f3116])).

fof(f3194,plain,(
    ! [X4,X5,X3] :
      ( g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK2))
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r1_lattice3(sK3,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | r1_lattice3(X5,X3,X4) ) ),
    inference(forward_demodulation,[],[f3193,f3147])).

fof(f3193,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | ~ r1_lattice3(sK3,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(u1_struct_0(X5),u1_orders_2(X5))
      | ~ l1_orders_2(X5)
      | r1_lattice3(X5,X3,X4) ) ),
    inference(forward_demodulation,[],[f3191,f3116])).

fof(f3191,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_lattice3(sK3,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(u1_struct_0(X5),u1_orders_2(X5))
      | ~ l1_orders_2(X5)
      | r1_lattice3(X5,X3,X4) ) ),
    inference(resolution,[],[f3099,f3054])).

fof(f3794,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK4,sK5(sK3,sK4,k2_yellow_0(sK2,sK4)))
    | ~ m1_subset_1(sK5(sK3,sK4,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f3793,f3057])).

fof(f3793,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | k2_yellow_0(sK2,sK4) = k2_yellow_0(sK3,sK4)
    | ~ r1_lattice3(sK2,sK4,sK5(sK3,sK4,k2_yellow_0(sK2,sK4)))
    | ~ m1_subset_1(sK5(sK3,sK4,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f3788,f3459])).

fof(f3788,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | ~ r1_lattice3(sK3,sK4,k2_yellow_0(sK2,sK4))
    | k2_yellow_0(sK2,sK4) = k2_yellow_0(sK3,sK4)
    | ~ r1_lattice3(sK2,sK4,sK5(sK3,sK4,k2_yellow_0(sK2,sK4)))
    | ~ m1_subset_1(sK5(sK3,sK4,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2)) ),
    inference(resolution,[],[f3248,f3552])).

fof(f3552,plain,(
    ! [X0] :
      ( r1_orders_2(sK3,X0,k2_yellow_0(sK2,sK4))
      | ~ r1_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f3551,f3053])).

fof(f3551,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK4,X0)
      | r1_orders_2(sK3,X0,k2_yellow_0(sK2,sK4))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f3394,f3058])).

fof(f3394,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK4,X0)
      | r1_orders_2(sK3,X0,k2_yellow_0(sK2,sK4)) ) ),
    inference(trivial_inequality_removal,[],[f3393])).

fof(f3393,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK4,X0)
      | r1_orders_2(sK3,X0,k2_yellow_0(sK2,sK4)) ) ),
    inference(forward_demodulation,[],[f3392,f3147])).

fof(f3392,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
      | ~ r1_lattice3(sK2,sK4,X0)
      | r1_orders_2(sK3,X0,k2_yellow_0(sK2,sK4)) ) ),
    inference(subsumption_resolution,[],[f3388,f3054])).

fof(f3388,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
      | ~ l1_orders_2(sK3)
      | ~ r1_lattice3(sK2,sK4,X0)
      | r1_orders_2(sK3,X0,k2_yellow_0(sK2,sK4)) ) ),
    inference(duplicate_literal_removal,[],[f3387])).

fof(f3387,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
      | ~ l1_orders_2(sK3)
      | ~ r1_lattice3(sK2,sK4,X0)
      | r1_orders_2(sK3,X0,k2_yellow_0(sK2,sK4)) ) ),
    inference(superposition,[],[f3334,f3116])).

fof(f3334,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(sK2,sK4,X1)
      | r1_orders_2(X0,X1,k2_yellow_0(sK2,sK4)) ) ),
    inference(subsumption_resolution,[],[f3332,f3053])).

fof(f3332,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK2)
      | ~ r1_lattice3(sK2,sK4,X1)
      | r1_orders_2(X0,X1,k2_yellow_0(sK2,sK4)) ) ),
    inference(resolution,[],[f3224,f3056])).

fof(f3224,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_yellow_0(X6,X7)
      | ~ m1_subset_1(k2_yellow_0(X6,X7),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | g1_orders_2(u1_struct_0(X6),u1_orders_2(X6)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
      | ~ l1_orders_2(X4)
      | ~ l1_orders_2(X6)
      | ~ r1_lattice3(X6,X7,X5)
      | r1_orders_2(X4,X5,k2_yellow_0(X6,X7)) ) ),
    inference(subsumption_resolution,[],[f3221,f3058])).

fof(f3221,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_orders_2(X4,X5,k2_yellow_0(X6,X7))
      | ~ m1_subset_1(k2_yellow_0(X6,X7),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(k2_yellow_0(X6,X7),u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | g1_orders_2(u1_struct_0(X6),u1_orders_2(X6)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
      | ~ l1_orders_2(X4)
      | ~ l1_orders_2(X6)
      | ~ r1_lattice3(X6,X7,X5)
      | ~ r2_yellow_0(X6,X7) ) ),
    inference(duplicate_literal_removal,[],[f3220])).

fof(f3220,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_orders_2(X4,X5,k2_yellow_0(X6,X7))
      | ~ m1_subset_1(k2_yellow_0(X6,X7),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(k2_yellow_0(X6,X7),u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | g1_orders_2(u1_struct_0(X6),u1_orders_2(X6)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
      | ~ l1_orders_2(X4)
      | ~ l1_orders_2(X6)
      | ~ r1_lattice3(X6,X7,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ r2_yellow_0(X6,X7)
      | ~ l1_orders_2(X6) ) ),
    inference(resolution,[],[f3104,f3105])).

fof(f3105,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f3097,f3058])).

fof(f3097,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3060])).

fof(f3060,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3104,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r1_orders_2(X0,X4,X5)
      | r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3103])).

fof(f3103,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3091])).

fof(f3091,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3027])).

fof(f3027,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3026])).

fof(f3026,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2988])).

fof(f2988,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_0)).

fof(f3248,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK3,sK5(sK3,sK4,X0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_lattice3(sK3,sK4,X0)
      | k2_yellow_0(sK3,sK4) = X0 ) ),
    inference(forward_demodulation,[],[f3247,f3116])).

fof(f3247,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK3,sK5(sK3,sK4,X0),X0)
      | ~ r1_lattice3(sK3,sK4,X0)
      | k2_yellow_0(sK3,sK4) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f3244,f3054])).

fof(f3244,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK3,sK5(sK3,sK4,X0),X0)
      | ~ r1_lattice3(sK3,sK4,X0)
      | k2_yellow_0(sK3,sK4) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l1_orders_2(sK3) ) ),
    inference(resolution,[],[f3238,f3063])).

fof(f3063,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3828,plain,
    ( m1_subset_1(sK5(sK3,sK4,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f3821,f3057])).

fof(f3821,plain,
    ( k2_yellow_0(sK2,sK4) = k2_yellow_0(sK3,sK4)
    | m1_subset_1(sK5(sK3,sK4,k2_yellow_0(sK2,sK4)),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(resolution,[],[f3556,f3459])).

fof(f3556,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK3,sK4,X0)
      | k2_yellow_0(sK3,sK4) = X0
      | m1_subset_1(sK5(sK3,sK4,X0),u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f3139,f3238])).
%------------------------------------------------------------------------------
