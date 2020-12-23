%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1524+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:22 EST 2020

% Result     : Theorem 4.14s
% Output     : Refutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :  138 (1340 expanded)
%              Number of leaves         :   17 ( 542 expanded)
%              Depth                    :   29
%              Number of atoms          :  596 (11941 expanded)
%              Number of equality atoms :   53 (2340 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8837,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3149,f3154,f3159,f3160,f8770,f8836])).

fof(f8836,plain,
    ( spl18_2
    | ~ spl18_4 ),
    inference(avatar_contradiction_clause,[],[f8835])).

fof(f8835,plain,
    ( $false
    | spl18_2
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f8834,f3136])).

fof(f3136,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(definition_unfolding,[],[f3072,f3074])).

fof(f3074,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f3031])).

fof(f3031,plain,
    ( ( ( ~ r1_lattice3(sK1,sK2,sK4)
        & r1_lattice3(sK0,sK2,sK3) )
      | ( ~ r2_lattice3(sK1,sK2,sK4)
        & r2_lattice3(sK0,sK2,sK3) ) )
    & sK3 = sK4
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f2986,f3030,f3029,f3028,f3027])).

fof(f3027,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ( ( ~ r1_lattice3(X1,X2,X4)
                        & r1_lattice3(X0,X2,X3) )
                      | ( ~ r2_lattice3(X1,X2,X4)
                        & r2_lattice3(X0,X2,X3) ) )
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ( ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(sK0,X2,X3) )
                    | ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(sK0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3028,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( ? [X4] :
                ( ( ( ~ r1_lattice3(X1,X2,X4)
                    & r1_lattice3(sK0,X2,X3) )
                  | ( ~ r2_lattice3(X1,X2,X4)
                    & r2_lattice3(sK0,X2,X3) ) )
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1) )
   => ( ? [X3,X2] :
          ( ? [X4] :
              ( ( ( ~ r1_lattice3(sK1,X2,X4)
                  & r1_lattice3(sK0,X2,X3) )
                | ( ~ r2_lattice3(sK1,X2,X4)
                  & r2_lattice3(sK0,X2,X3) ) )
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3029,plain,
    ( ? [X3,X2] :
        ( ? [X4] :
            ( ( ( ~ r1_lattice3(sK1,X2,X4)
                & r1_lattice3(sK0,X2,X3) )
              | ( ~ r2_lattice3(sK1,X2,X4)
                & r2_lattice3(sK0,X2,X3) ) )
            & X3 = X4
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ? [X4] :
          ( ( ( ~ r1_lattice3(sK1,sK2,X4)
              & r1_lattice3(sK0,sK2,sK3) )
            | ( ~ r2_lattice3(sK1,sK2,X4)
              & r2_lattice3(sK0,sK2,sK3) ) )
          & sK3 = X4
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3030,plain,
    ( ? [X4] :
        ( ( ( ~ r1_lattice3(sK1,sK2,X4)
            & r1_lattice3(sK0,sK2,sK3) )
          | ( ~ r2_lattice3(sK1,sK2,X4)
            & r2_lattice3(sK0,sK2,sK3) ) )
        & sK3 = X4
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ( ( ~ r1_lattice3(sK1,sK2,sK4)
          & r1_lattice3(sK0,sK2,sK3) )
        | ( ~ r2_lattice3(sK1,sK2,sK4)
          & r2_lattice3(sK0,sK2,sK3) ) )
      & sK3 = sK4
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f2986,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) )
                    | ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f2985])).

fof(f2985,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) )
                    | ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2965])).

fof(f2965,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f2964])).

fof(f2964,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_0)).

fof(f3072,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3031])).

fof(f8834,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | spl18_2
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f8833,f3148])).

fof(f3148,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | spl18_2 ),
    inference(avatar_component_clause,[],[f3146])).

fof(f3146,plain,
    ( spl18_2
  <=> r1_lattice3(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f8833,plain,
    ( r1_lattice3(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | spl18_2
    | ~ spl18_4 ),
    inference(resolution,[],[f8824,f3360])).

fof(f3360,plain,(
    ! [X4,X5] :
      ( m1_subset_1(sK5(sK1,X4,X5),u1_struct_0(sK0))
      | r1_lattice3(sK1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3356,f3070])).

fof(f3070,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f3031])).

fof(f3356,plain,(
    ! [X4,X5] :
      ( m1_subset_1(sK5(sK1,X4,X5),u1_struct_0(sK0))
      | r1_lattice3(sK1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f3080,f3348])).

fof(f3348,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f3346])).

fof(f3346,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != k7_lattice3(k7_lattice3(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(superposition,[],[f3238,f3170])).

fof(f3170,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = k7_lattice3(k7_lattice3(sK0)) ),
    inference(resolution,[],[f3069,f3128])).

fof(f3128,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f3024])).

fof(f3024,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2961])).

fof(f2961,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_lattice3)).

fof(f3069,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3031])).

fof(f3238,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != k7_lattice3(k7_lattice3(sK0))
      | u1_struct_0(sK1) = X2 ) ),
    inference(global_subsumption,[],[f3198,f3235])).

fof(f3235,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != k7_lattice3(k7_lattice3(sK0))
      | u1_struct_0(sK1) = X2
      | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f3120,f3227])).

fof(f3227,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = k7_lattice3(k7_lattice3(sK0)) ),
    inference(backward_demodulation,[],[f3071,f3170])).

fof(f3071,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f3031])).

fof(f3120,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f3017])).

fof(f3017,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f3198,plain,(
    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f3070,f3131])).

fof(f3131,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f3026])).

fof(f3026,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f3080,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3035])).

fof(f3035,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3033,f3034])).

fof(f3034,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3033,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3032])).

fof(f3032,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f2988])).

fof(f2988,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2987])).

fof(f2987,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2831])).

fof(f2831,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f8824,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK4),u1_struct_0(sK0))
    | spl18_2
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f8823,f3136])).

fof(f8823,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | spl18_2
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f8822,f3148])).

fof(f8822,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK4),u1_struct_0(sK0))
    | r1_lattice3(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl18_4 ),
    inference(duplicate_literal_removal,[],[f8821])).

fof(f8821,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK4),u1_struct_0(sK0))
    | r1_lattice3(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | r1_lattice3(sK1,sK2,sK4)
    | ~ spl18_4 ),
    inference(resolution,[],[f8792,f3665])).

fof(f3665,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK5(sK1,X3,X4),X3)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r1_lattice3(sK1,X3,X4) ) ),
    inference(forward_demodulation,[],[f3188,f3348])).

fof(f3188,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK5(sK1,X3,X4),X3)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | r1_lattice3(sK1,X3,X4) ) ),
    inference(resolution,[],[f3070,f3081])).

fof(f3081,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3035])).

fof(f8792,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1,X0,sK4),sK2)
        | ~ m1_subset_1(sK5(sK1,X0,sK4),u1_struct_0(sK0))
        | r1_lattice3(sK1,X0,sK4) )
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f8787,f3136])).

fof(f8787,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1,X0,sK4),sK2)
        | ~ m1_subset_1(sK5(sK1,X0,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | r1_lattice3(sK1,X0,sK4) )
    | ~ spl18_4 ),
    inference(resolution,[],[f8786,f3676])).

fof(f3676,plain,(
    ! [X6,X5] :
      ( ~ r1_orders_2(sK1,X5,sK5(sK1,X6,X5))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r1_lattice3(sK1,X6,X5) ) ),
    inference(forward_demodulation,[],[f3189,f3348])).

fof(f3189,plain,(
    ! [X6,X5] :
      ( ~ r1_orders_2(sK1,X5,sK5(sK1,X6,X5))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | r1_lattice3(sK1,X6,X5) ) ),
    inference(resolution,[],[f3070,f3082])).

fof(f3082,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3035])).

fof(f8786,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK4,X0)
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f8785,f3136])).

fof(f8785,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | r1_orders_2(sK1,sK4,X0) )
    | ~ spl18_4 ),
    inference(duplicate_literal_removal,[],[f8781])).

fof(f8781,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | r1_orders_2(sK1,sK4,X0) )
    | ~ spl18_4 ),
    inference(resolution,[],[f8780,f3611])).

fof(f3611,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK1,X0,X1) ) ),
    inference(forward_demodulation,[],[f3610,f3348])).

fof(f3610,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | r1_orders_2(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f3609,f3348])).

fof(f3609,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | r1_orders_2(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3608,f3070])).

fof(f3608,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | r1_orders_2(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f3130,f3599])).

fof(f3599,plain,(
    u1_orders_2(sK0) = u1_orders_2(sK1) ),
    inference(trivial_inequality_removal,[],[f3597])).

fof(f3597,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != k7_lattice3(k7_lattice3(sK0))
    | u1_orders_2(sK0) = u1_orders_2(sK1) ),
    inference(superposition,[],[f3239,f3170])).

fof(f3239,plain,(
    ! [X6,X7] :
      ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(X6,X7)
      | u1_orders_2(sK1) = X7 ) ),
    inference(global_subsumption,[],[f3198,f3237])).

fof(f3237,plain,(
    ! [X6,X7] :
      ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(X6,X7)
      | u1_orders_2(sK1) = X7
      | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f3121,f3227])).

fof(f3121,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f3017])).

fof(f3130,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3066])).

fof(f3066,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3025])).

fof(f3025,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1885])).

fof(f1885,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f8780,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(sK4,X3),u1_orders_2(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK2) )
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f8776,f3136])).

fof(f8776,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(sK4,X3),u1_orders_2(sK0)) )
    | ~ spl18_4 ),
    inference(duplicate_literal_removal,[],[f8775])).

fof(f8775,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(sK4,X3),u1_orders_2(sK0)) )
    | ~ spl18_4 ),
    inference(resolution,[],[f8772,f3171])).

fof(f3171,plain,(
    ! [X17,X16] :
      ( ~ r1_orders_2(sK0,X16,X17)
      | ~ m1_subset_1(X17,u1_struct_0(sK0))
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X16,X17),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f3069,f3129])).

fof(f3129,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ),
    inference(cnf_transformation,[],[f3066])).

fof(f8772,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK4,X0)
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f8771,f3136])).

fof(f8771,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK4,X0) )
    | ~ spl18_4 ),
    inference(resolution,[],[f3158,f3161])).

fof(f3161,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK0,X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK0,X2,X0) ) ),
    inference(resolution,[],[f3069,f3079])).

fof(f3079,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f3035])).

fof(f3158,plain,
    ( r1_lattice3(sK0,sK2,sK4)
    | ~ spl18_4 ),
    inference(avatar_component_clause,[],[f3156])).

fof(f3156,plain,
    ( spl18_4
  <=> r1_lattice3(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f8770,plain,
    ( spl18_1
    | ~ spl18_3 ),
    inference(avatar_contradiction_clause,[],[f8769])).

fof(f8769,plain,
    ( $false
    | spl18_1
    | ~ spl18_3 ),
    inference(subsumption_resolution,[],[f8768,f3136])).

fof(f8768,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | spl18_1
    | ~ spl18_3 ),
    inference(subsumption_resolution,[],[f8767,f3144])).

fof(f3144,plain,
    ( ~ r2_lattice3(sK1,sK2,sK4)
    | spl18_1 ),
    inference(avatar_component_clause,[],[f3142])).

fof(f3142,plain,
    ( spl18_1
  <=> r2_lattice3(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f8767,plain,
    ( r2_lattice3(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | spl18_1
    | ~ spl18_3 ),
    inference(resolution,[],[f8765,f3359])).

fof(f3359,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK6(sK1,X2,X3),u1_struct_0(sK0))
      | r2_lattice3(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3355,f3070])).

fof(f3355,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK6(sK1,X2,X3),u1_struct_0(sK0))
      | r2_lattice3(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f3084,f3348])).

fof(f3084,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3039])).

fof(f3039,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
                & r2_hidden(sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f3037,f3038])).

fof(f3038,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3037,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3036])).

fof(f3036,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f2990])).

fof(f2990,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2989])).

fof(f2989,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2832])).

fof(f2832,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f8765,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK4),u1_struct_0(sK0))
    | spl18_1
    | ~ spl18_3 ),
    inference(subsumption_resolution,[],[f8764,f3136])).

fof(f8764,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | spl18_1
    | ~ spl18_3 ),
    inference(subsumption_resolution,[],[f8763,f3144])).

fof(f8763,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK4),u1_struct_0(sK0))
    | r2_lattice3(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl18_3 ),
    inference(duplicate_literal_removal,[],[f8762])).

fof(f8762,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK4),u1_struct_0(sK0))
    | r2_lattice3(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | r2_lattice3(sK1,sK2,sK4)
    | ~ spl18_3 ),
    inference(resolution,[],[f5981,f3666])).

fof(f3666,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK6(sK1,X10,X11),X10)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | r2_lattice3(sK1,X10,X11) ) ),
    inference(forward_demodulation,[],[f3191,f3348])).

fof(f3191,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK6(sK1,X10,X11),X10)
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | r2_lattice3(sK1,X10,X11) ) ),
    inference(resolution,[],[f3070,f3085])).

fof(f3085,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3039])).

fof(f5981,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(sK1,X3,sK4),sK2)
        | ~ m1_subset_1(sK6(sK1,X3,sK4),u1_struct_0(sK0))
        | r2_lattice3(sK1,X3,sK4) )
    | ~ spl18_3 ),
    inference(subsumption_resolution,[],[f5977,f3136])).

fof(f5977,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK6(sK1,X3,sK4),u1_struct_0(sK0))
        | ~ r2_hidden(sK6(sK1,X3,sK4),sK2)
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | r2_lattice3(sK1,X3,sK4) )
    | ~ spl18_3 ),
    inference(resolution,[],[f5974,f3678])).

fof(f3678,plain,(
    ! [X12,X13] :
      ( ~ r1_orders_2(sK1,sK6(sK1,X12,X13),X13)
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | r2_lattice3(sK1,X12,X13) ) ),
    inference(forward_demodulation,[],[f3192,f3348])).

fof(f3192,plain,(
    ! [X12,X13] :
      ( ~ r1_orders_2(sK1,sK6(sK1,X12,X13),X13)
      | ~ m1_subset_1(X13,u1_struct_0(sK1))
      | r2_lattice3(sK1,X12,X13) ) ),
    inference(resolution,[],[f3070,f3086])).

fof(f3086,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3039])).

fof(f5974,plain,
    ( ! [X3] :
        ( r1_orders_2(sK1,X3,sK4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK2) )
    | ~ spl18_3 ),
    inference(subsumption_resolution,[],[f5973,f3136])).

fof(f5973,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK1,X3,sK4)
        | ~ r2_hidden(X3,sK2) )
    | ~ spl18_3 ),
    inference(duplicate_literal_removal,[],[f5963])).

fof(f5963,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK1,X3,sK4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK2) )
    | ~ spl18_3 ),
    inference(resolution,[],[f3611,f3731])).

fof(f3731,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK4),u1_orders_2(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl18_3 ),
    inference(subsumption_resolution,[],[f3730,f3136])).

fof(f3730,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,sK4),u1_orders_2(sK0)) )
    | ~ spl18_3 ),
    inference(duplicate_literal_removal,[],[f3728])).

fof(f3728,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,sK4),u1_orders_2(sK0)) )
    | ~ spl18_3 ),
    inference(resolution,[],[f3727,f3171])).

fof(f3727,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK4)
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_3 ),
    inference(subsumption_resolution,[],[f3725,f3136])).

fof(f3725,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK4) )
    | ~ spl18_3 ),
    inference(resolution,[],[f3164,f3153])).

fof(f3153,plain,
    ( r2_lattice3(sK0,sK2,sK4)
    | ~ spl18_3 ),
    inference(avatar_component_clause,[],[f3151])).

fof(f3151,plain,
    ( spl18_3
  <=> r2_lattice3(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).

fof(f3164,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_lattice3(sK0,X8,X9)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r2_hidden(X7,X8)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r1_orders_2(sK0,X7,X9) ) ),
    inference(resolution,[],[f3069,f3083])).

fof(f3083,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2) ) ),
    inference(cnf_transformation,[],[f3039])).

fof(f3160,plain,
    ( spl18_3
    | spl18_4 ),
    inference(avatar_split_clause,[],[f3135,f3156,f3151])).

fof(f3135,plain,
    ( r1_lattice3(sK0,sK2,sK4)
    | r2_lattice3(sK0,sK2,sK4) ),
    inference(definition_unfolding,[],[f3075,f3074,f3074])).

fof(f3075,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f3031])).

fof(f3159,plain,
    ( ~ spl18_1
    | spl18_4 ),
    inference(avatar_split_clause,[],[f3134,f3156,f3142])).

fof(f3134,plain,
    ( r1_lattice3(sK0,sK2,sK4)
    | ~ r2_lattice3(sK1,sK2,sK4) ),
    inference(definition_unfolding,[],[f3076,f3074])).

fof(f3076,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f3031])).

fof(f3154,plain,
    ( spl18_3
    | ~ spl18_2 ),
    inference(avatar_split_clause,[],[f3133,f3146,f3151])).

fof(f3133,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | r2_lattice3(sK0,sK2,sK4) ),
    inference(definition_unfolding,[],[f3077,f3074])).

fof(f3077,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | r2_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f3031])).

fof(f3149,plain,
    ( ~ spl18_1
    | ~ spl18_2 ),
    inference(avatar_split_clause,[],[f3078,f3146,f3142])).

fof(f3078,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | ~ r2_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f3031])).
%------------------------------------------------------------------------------
