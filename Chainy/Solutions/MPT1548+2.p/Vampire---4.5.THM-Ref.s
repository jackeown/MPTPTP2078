%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1548+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:23 EST 2020

% Result     : Theorem 4.72s
% Output     : Refutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :  211 (4335 expanded)
%              Number of leaves         :   26 (1539 expanded)
%              Depth                    :   36
%              Number of atoms          : 1068 (20057 expanded)
%              Number of equality atoms :  188 (7661 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10288,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3502,f4579,f6283,f7258,f7378,f7388,f10285])).

fof(f10285,plain,
    ( ~ spl15_18
    | ~ spl15_53 ),
    inference(avatar_contradiction_clause,[],[f10284])).

fof(f10284,plain,
    ( $false
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(subsumption_resolution,[],[f10283,f3315])).

fof(f3315,plain,(
    ! [X9] : m1_subset_1(k1_yellow_0(sK3,X9),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f3312,f3086])).

fof(f3086,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f3055])).

fof(f3055,plain,
    ( k1_yellow_0(sK2,sK4) != k1_yellow_0(sK3,sK4)
    & r1_yellow_0(sK2,sK4)
    & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    & l1_orders_2(sK3)
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f3020,f3054,f3053,f3052])).

fof(f3052,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                & r1_yellow_0(X0,X2) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X1,X2) != k1_yellow_0(sK2,X2)
              & r1_yellow_0(sK2,X2) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
          & l1_orders_2(X1) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3053,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_yellow_0(X1,X2) != k1_yellow_0(sK2,X2)
            & r1_yellow_0(sK2,X2) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( k1_yellow_0(sK2,X2) != k1_yellow_0(sK3,X2)
          & r1_yellow_0(sK2,X2) )
      & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      & l1_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3054,plain,
    ( ? [X2] :
        ( k1_yellow_0(sK2,X2) != k1_yellow_0(sK3,X2)
        & r1_yellow_0(sK2,X2) )
   => ( k1_yellow_0(sK2,sK4) != k1_yellow_0(sK3,sK4)
      & r1_yellow_0(sK2,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3020,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
              & r1_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f3019])).

fof(f3019,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
              & r1_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2994])).

fof(f2994,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( r1_yellow_0(X0,X2)
                 => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f2993])).

fof(f2993,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r1_yellow_0(X0,X2)
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_0)).

fof(f3312,plain,(
    ! [X9] :
      ( m1_subset_1(k1_yellow_0(sK3,X9),u1_struct_0(sK2))
      | ~ l1_orders_2(sK3) ) ),
    inference(superposition,[],[f3090,f3299])).

fof(f3299,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(trivial_inequality_removal,[],[f3298])).

fof(f3298,plain,
    ( k7_lattice3(k7_lattice3(sK2)) != k7_lattice3(k7_lattice3(sK2))
    | u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(superposition,[],[f3208,f3196])).

fof(f3196,plain,(
    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = k7_lattice3(k7_lattice3(sK2)) ),
    inference(backward_demodulation,[],[f3087,f3158])).

fof(f3158,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = k7_lattice3(k7_lattice3(sK2)) ),
    inference(resolution,[],[f3085,f3140])).

fof(f3140,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f3046])).

fof(f3046,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2961])).

fof(f2961,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_lattice3)).

fof(f3085,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3055])).

fof(f3087,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f3055])).

fof(f3208,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK2))
      | u1_struct_0(sK2) = X0 ) ),
    inference(forward_demodulation,[],[f3199,f3158])).

fof(f3199,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | u1_struct_0(sK2) = X0 ) ),
    inference(resolution,[],[f3160,f3130])).

fof(f3130,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f3036])).

fof(f3036,plain,(
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

fof(f3160,plain,(
    m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(resolution,[],[f3085,f3143])).

fof(f3143,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f3048])).

fof(f3048,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f3090,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3021])).

fof(f3021,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2973])).

fof(f2973,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f10283,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK2))
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(subsumption_resolution,[],[f10282,f4427])).

fof(f4427,plain,(
    r2_lattice3(sK2,sK4,k1_yellow_0(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f4426,f3085])).

fof(f4426,plain,
    ( ~ l1_orders_2(sK2)
    | r2_lattice3(sK2,sK4,k1_yellow_0(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f4422,f3158])).

fof(f4422,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != k7_lattice3(k7_lattice3(sK2))
    | ~ l1_orders_2(sK2)
    | r2_lattice3(sK2,sK4,k1_yellow_0(sK3,sK4)) ),
    inference(resolution,[],[f3592,f3315])).

fof(f3592,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK2))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,sK4,k1_yellow_0(sK3,sK4)) ) ),
    inference(subsumption_resolution,[],[f3590,f3315])).

fof(f3590,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK2))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK2))
      | ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,sK4,k1_yellow_0(sK3,sK4)) ) ),
    inference(resolution,[],[f3583,f3439])).

fof(f3439,plain,(
    r2_lattice3(sK3,sK4,k1_yellow_0(sK3,sK4)) ),
    inference(resolution,[],[f3428,f3380])).

fof(f3380,plain,(
    ! [X12] :
      ( ~ r1_yellow_0(sK3,X12)
      | r2_lattice3(sK3,X12,k1_yellow_0(sK3,X12)) ) ),
    inference(subsumption_resolution,[],[f3301,f3315])).

fof(f3301,plain,(
    ! [X12] :
      ( ~ m1_subset_1(k1_yellow_0(sK3,X12),u1_struct_0(sK2))
      | ~ r1_yellow_0(sK3,X12)
      | r2_lattice3(sK3,X12,k1_yellow_0(sK3,X12)) ) ),
    inference(backward_demodulation,[],[f3176,f3299])).

fof(f3176,plain,(
    ! [X12] :
      ( ~ r1_yellow_0(sK3,X12)
      | ~ m1_subset_1(k1_yellow_0(sK3,X12),u1_struct_0(sK3))
      | r2_lattice3(sK3,X12,k1_yellow_0(sK3,X12)) ) ),
    inference(resolution,[],[f3086,f3146])).

fof(f3146,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f3091])).

fof(f3091,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3060])).

fof(f3060,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_lattice3(X0,X1,sK5(X0,X1,X2))
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3058,f3059])).

fof(f3059,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3058,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3057])).

fof(f3057,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3056])).

fof(f3056,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3023])).

fof(f3023,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3022])).

fof(f3022,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2972])).

fof(f2972,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f3428,plain,(
    r1_yellow_0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f3427,f3158])).

fof(f3427,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != k7_lattice3(k7_lattice3(sK2))
    | r1_yellow_0(sK3,sK4) ),
    inference(forward_demodulation,[],[f3426,f3299])).

fof(f3426,plain,
    ( k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK2))
    | r1_yellow_0(sK3,sK4) ),
    inference(forward_demodulation,[],[f3421,f3379])).

fof(f3379,plain,(
    u1_orders_2(sK2) = u1_orders_2(sK3) ),
    inference(trivial_inequality_removal,[],[f3378])).

fof(f3378,plain,
    ( k7_lattice3(k7_lattice3(sK2)) != k7_lattice3(k7_lattice3(sK2))
    | u1_orders_2(sK2) = u1_orders_2(sK3) ),
    inference(superposition,[],[f3209,f3302])).

fof(f3302,plain,(
    k7_lattice3(k7_lattice3(sK2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3)) ),
    inference(backward_demodulation,[],[f3196,f3299])).

fof(f3209,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != k7_lattice3(k7_lattice3(sK2))
      | u1_orders_2(sK2) = X3 ) ),
    inference(forward_demodulation,[],[f3200,f3158])).

fof(f3200,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | u1_orders_2(sK2) = X3 ) ),
    inference(resolution,[],[f3160,f3131])).

fof(f3131,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f3036])).

fof(f3421,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != k7_lattice3(k7_lattice3(sK2))
    | r1_yellow_0(sK3,sK4) ),
    inference(resolution,[],[f3296,f3086])).

fof(f3296,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK2))
      | r1_yellow_0(X0,sK4) ) ),
    inference(resolution,[],[f3295,f3088])).

fof(f3088,plain,(
    r1_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f3055])).

fof(f3295,plain,(
    ! [X4,X5] :
      ( ~ r1_yellow_0(sK2,X4)
      | g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) != k7_lattice3(k7_lattice3(sK2))
      | ~ l1_orders_2(X5)
      | r1_yellow_0(X5,X4) ) ),
    inference(forward_demodulation,[],[f3156,f3158])).

fof(f3156,plain,(
    ! [X4,X5] :
      ( ~ r1_yellow_0(sK2,X4)
      | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X5),u1_orders_2(X5))
      | ~ l1_orders_2(X5)
      | r1_yellow_0(X5,X4) ) ),
    inference(resolution,[],[f3085,f3117])).

fof(f3117,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | r1_yellow_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f3027])).

fof(f3027,plain,(
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
    inference(flattening,[],[f3026])).

fof(f3026,plain,(
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
    inference(ennf_transformation,[],[f2980])).

fof(f2980,axiom,(
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

fof(f3583,plain,(
    ! [X17,X18,X16] :
      ( ~ r2_lattice3(sK3,X16,X17)
      | ~ m1_subset_1(X17,u1_struct_0(sK2))
      | k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(X18),u1_orders_2(X18))
      | ~ m1_subset_1(X17,u1_struct_0(X18))
      | ~ l1_orders_2(X18)
      | r2_lattice3(X18,X16,X17) ) ),
    inference(forward_demodulation,[],[f3582,f3158])).

fof(f3582,plain,(
    ! [X17,X18,X16] :
      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X18),u1_orders_2(X18))
      | ~ m1_subset_1(X17,u1_struct_0(sK2))
      | ~ r2_lattice3(sK3,X16,X17)
      | ~ m1_subset_1(X17,u1_struct_0(X18))
      | ~ l1_orders_2(X18)
      | r2_lattice3(X18,X16,X17) ) ),
    inference(forward_demodulation,[],[f3581,f3299])).

fof(f3581,plain,(
    ! [X17,X18,X16] :
      ( g1_orders_2(u1_struct_0(X18),u1_orders_2(X18)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK2))
      | ~ m1_subset_1(X17,u1_struct_0(sK2))
      | ~ r2_lattice3(sK3,X16,X17)
      | ~ m1_subset_1(X17,u1_struct_0(X18))
      | ~ l1_orders_2(X18)
      | r2_lattice3(X18,X16,X17) ) ),
    inference(forward_demodulation,[],[f3580,f3379])).

fof(f3580,plain,(
    ! [X17,X18,X16] :
      ( ~ m1_subset_1(X17,u1_struct_0(sK2))
      | ~ r2_lattice3(sK3,X16,X17)
      | ~ m1_subset_1(X17,u1_struct_0(X18))
      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(u1_struct_0(X18),u1_orders_2(X18))
      | ~ l1_orders_2(X18)
      | r2_lattice3(X18,X16,X17) ) ),
    inference(forward_demodulation,[],[f3178,f3299])).

fof(f3178,plain,(
    ! [X17,X18,X16] :
      ( ~ r2_lattice3(sK3,X16,X17)
      | ~ m1_subset_1(X17,u1_struct_0(X18))
      | ~ m1_subset_1(X17,u1_struct_0(sK3))
      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(u1_struct_0(X18),u1_orders_2(X18))
      | ~ l1_orders_2(X18)
      | r2_lattice3(X18,X16,X17) ) ),
    inference(resolution,[],[f3086,f3148])).

fof(f3148,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | r2_lattice3(X1,X2,X4) ) ),
    inference(equality_resolution,[],[f3135])).

fof(f3135,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3041])).

fof(f3041,plain,(
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
    inference(flattening,[],[f3040])).

fof(f3040,plain,(
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
    inference(ennf_transformation,[],[f2995])).

fof(f2995,axiom,(
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

fof(f10282,plain,
    ( ~ r2_lattice3(sK2,sK4,k1_yellow_0(sK3,sK4))
    | ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK2))
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(subsumption_resolution,[],[f10280,f3089])).

fof(f3089,plain,(
    k1_yellow_0(sK2,sK4) != k1_yellow_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f3055])).

fof(f10280,plain,
    ( k1_yellow_0(sK2,sK4) = k1_yellow_0(sK3,sK4)
    | ~ r2_lattice3(sK2,sK4,k1_yellow_0(sK3,sK4))
    | ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK2))
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(resolution,[],[f10277,f7397])).

fof(f7397,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK2,X2,sK9(sK2,sK4,X2))
        | k1_yellow_0(sK2,sK4) = X2
        | ~ r2_lattice3(sK2,sK4,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
    | ~ spl15_18 ),
    inference(backward_demodulation,[],[f3189,f3739])).

fof(f3739,plain,
    ( k1_yellow_0(sK2,sK4) = sK8(sK2,sK4)
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f3737])).

fof(f3737,plain,
    ( spl15_18
  <=> k1_yellow_0(sK2,sK4) = sK8(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f3189,plain,(
    ! [X2] :
      ( ~ r1_orders_2(sK2,X2,sK9(sK2,sK4,X2))
      | ~ r2_lattice3(sK2,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | sK8(sK2,sK4) = X2 ) ),
    inference(resolution,[],[f3185,f3103])).

fof(f3103,plain,(
    ! [X0,X7,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_orders_2(X0,X7,sK9(X0,X1,X7))
      | ~ r2_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | sK8(X0,X1) = X7 ) ),
    inference(cnf_transformation,[],[f3068])).

fof(f3068,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ( sK6(X0,X1,X2) != X2
              & ! [X4] :
                  ( r1_orders_2(X0,sK6(X0,X1,X2),X4)
                  | ~ r2_lattice3(X0,X1,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK6(X0,X1,X2))
              & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
            | ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
              & r2_lattice3(X0,X1,sK7(X0,X1,X2))
              & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ( ! [X7] :
              ( sK8(X0,X1) = X7
              | ( ~ r1_orders_2(X0,X7,sK9(X0,X1,X7))
                & r2_lattice3(X0,X1,sK9(X0,X1,X7))
                & m1_subset_1(sK9(X0,X1,X7),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X7)
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & ! [X9] :
              ( r1_orders_2(X0,sK8(X0,X1),X9)
              | ~ r2_lattice3(X0,X1,X9)
              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,sK8(X0,X1))
          & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f3063,f3067,f3066,f3065,f3064])).

fof(f3064,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X2 != X3
          & ! [X4] :
              ( r1_orders_2(X0,X3,X4)
              | ~ r2_lattice3(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK6(X0,X1,X2) != X2
        & ! [X4] :
            ( r1_orders_2(X0,sK6(X0,X1,X2),X4)
            | ~ r2_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3065,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X2,X5)
          & r2_lattice3(X0,X1,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
        & r2_lattice3(X0,X1,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3066,plain,(
    ! [X1,X0] :
      ( ? [X6] :
          ( ! [X7] :
              ( X6 = X7
              | ? [X8] :
                  ( ~ r1_orders_2(X0,X7,X8)
                  & r2_lattice3(X0,X1,X8)
                  & m1_subset_1(X8,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X7)
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & ! [X9] :
              ( r1_orders_2(X0,X6,X9)
              | ~ r2_lattice3(X0,X1,X9)
              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( ! [X7] :
            ( sK8(X0,X1) = X7
            | ? [X8] :
                ( ~ r1_orders_2(X0,X7,X8)
                & r2_lattice3(X0,X1,X8)
                & m1_subset_1(X8,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X7)
            | ~ m1_subset_1(X7,u1_struct_0(X0)) )
        & ! [X9] :
            ( r1_orders_2(X0,sK8(X0,X1),X9)
            | ~ r2_lattice3(X0,X1,X9)
            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK8(X0,X1))
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3067,plain,(
    ! [X7,X1,X0] :
      ( ? [X8] :
          ( ~ r1_orders_2(X0,X7,X8)
          & r2_lattice3(X0,X1,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X7,sK9(X0,X1,X7))
        & r2_lattice3(X0,X1,sK9(X0,X1,X7))
        & m1_subset_1(sK9(X0,X1,X7),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3063,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ? [X3] :
                ( X2 != X3
                & ! [X4] :
                    ( r1_orders_2(X0,X3,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ? [X5] :
                ( ~ r1_orders_2(X0,X2,X5)
                & r2_lattice3(X0,X1,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X6] :
            ( ! [X7] :
                ( X6 = X7
                | ? [X8] :
                    ( ~ r1_orders_2(X0,X7,X8)
                    & r2_lattice3(X0,X1,X8)
                    & m1_subset_1(X8,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X7)
                | ~ m1_subset_1(X7,u1_struct_0(X0)) )
            & ! [X9] :
                ( r1_orders_2(X0,X6,X9)
                | ~ r2_lattice3(X0,X1,X9)
                | ~ m1_subset_1(X9,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X6)
            & m1_subset_1(X6,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f3062])).

fof(f3062,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ? [X3] :
                ( X2 != X3
                & ! [X4] :
                    ( r1_orders_2(X0,X3,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ? [X5] :
                ( ~ r1_orders_2(X0,X2,X5)
                & r2_lattice3(X0,X1,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( ! [X3] :
                ( X2 = X3
                | ? [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    & r2_lattice3(X0,X1,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & ! [X5] :
                ( r1_orders_2(X0,X2,X5)
                | ~ r2_lattice3(X0,X1,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3049])).

fof(f3049,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ? [X2] :
          ( ! [X3] :
              ( X2 = X3
              | ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r2_lattice3(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & ! [X5] :
              ( r1_orders_2(X0,X2,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3185,plain,(
    sP0(sK2,sK4) ),
    inference(resolution,[],[f3181,f3088])).

fof(f3181,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK2,X0)
      | sP0(sK2,X0) ) ),
    inference(resolution,[],[f3155,f3096])).

fof(f3096,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ r1_yellow_0(X0,X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3061])).

fof(f3061,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f3050])).

fof(f3050,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3155,plain,(
    sP1(sK2) ),
    inference(resolution,[],[f3085,f3116])).

fof(f3116,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f3051])).

fof(f3051,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f3025,f3050,f3049])).

fof(f3025,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3024])).

fof(f3024,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3004])).

fof(f3004,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X2,X5) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f2970])).

fof(f2970,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_0)).

fof(f10277,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK3,sK4),sK9(sK2,sK4,k1_yellow_0(sK3,sK4)))
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(subsumption_resolution,[],[f10276,f3315])).

fof(f10276,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK2,k1_yellow_0(sK3,sK4),sK9(sK2,sK4,k1_yellow_0(sK3,sK4)))
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(subsumption_resolution,[],[f10274,f4512])).

fof(f4512,plain,
    ( m1_subset_1(sK9(sK2,sK4,k1_yellow_0(sK3,sK4)),u1_struct_0(sK2))
    | ~ spl15_53 ),
    inference(avatar_component_clause,[],[f4511])).

fof(f4511,plain,
    ( spl15_53
  <=> m1_subset_1(sK9(sK2,sK4,k1_yellow_0(sK3,sK4)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_53])])).

fof(f10274,plain,
    ( ~ m1_subset_1(sK9(sK2,sK4,k1_yellow_0(sK3,sK4)),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK2,k1_yellow_0(sK3,sK4),sK9(sK2,sK4,k1_yellow_0(sK3,sK4)))
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(resolution,[],[f10181,f3707])).

fof(f3707,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK3,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r1_orders_2(sK2,X2,X3) ) ),
    inference(subsumption_resolution,[],[f3699,f3158])).

fof(f3699,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r1_orders_2(sK3,X2,X3)
      | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != k7_lattice3(k7_lattice3(sK2))
      | r1_orders_2(sK2,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f3696])).

fof(f3696,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r1_orders_2(sK3,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != k7_lattice3(k7_lattice3(sK2))
      | r1_orders_2(sK2,X2,X3) ) ),
    inference(resolution,[],[f3691,f3085])).

fof(f3691,plain,(
    ! [X24,X23,X22] :
      ( ~ l1_orders_2(X24)
      | ~ m1_subset_1(X22,u1_struct_0(sK2))
      | ~ m1_subset_1(X23,u1_struct_0(sK2))
      | ~ r1_orders_2(sK3,X22,X23)
      | ~ m1_subset_1(X23,u1_struct_0(X24))
      | ~ m1_subset_1(X22,u1_struct_0(X24))
      | k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(X24),u1_orders_2(X24))
      | r1_orders_2(X24,X22,X23) ) ),
    inference(forward_demodulation,[],[f3690,f3158])).

fof(f3690,plain,(
    ! [X24,X23,X22] :
      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X24),u1_orders_2(X24))
      | ~ m1_subset_1(X22,u1_struct_0(sK2))
      | ~ m1_subset_1(X23,u1_struct_0(sK2))
      | ~ r1_orders_2(sK3,X22,X23)
      | ~ m1_subset_1(X23,u1_struct_0(X24))
      | ~ m1_subset_1(X22,u1_struct_0(X24))
      | ~ l1_orders_2(X24)
      | r1_orders_2(X24,X22,X23) ) ),
    inference(forward_demodulation,[],[f3689,f3299])).

fof(f3689,plain,(
    ! [X24,X23,X22] :
      ( g1_orders_2(u1_struct_0(X24),u1_orders_2(X24)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK2))
      | ~ m1_subset_1(X22,u1_struct_0(sK2))
      | ~ m1_subset_1(X23,u1_struct_0(sK2))
      | ~ r1_orders_2(sK3,X22,X23)
      | ~ m1_subset_1(X23,u1_struct_0(X24))
      | ~ m1_subset_1(X22,u1_struct_0(X24))
      | ~ l1_orders_2(X24)
      | r1_orders_2(X24,X22,X23) ) ),
    inference(forward_demodulation,[],[f3688,f3379])).

fof(f3688,plain,(
    ! [X24,X23,X22] :
      ( ~ m1_subset_1(X22,u1_struct_0(sK2))
      | ~ m1_subset_1(X23,u1_struct_0(sK2))
      | ~ r1_orders_2(sK3,X22,X23)
      | ~ m1_subset_1(X23,u1_struct_0(X24))
      | ~ m1_subset_1(X22,u1_struct_0(X24))
      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(u1_struct_0(X24),u1_orders_2(X24))
      | ~ l1_orders_2(X24)
      | r1_orders_2(X24,X22,X23) ) ),
    inference(forward_demodulation,[],[f3687,f3299])).

fof(f3687,plain,(
    ! [X24,X23,X22] :
      ( ~ m1_subset_1(X23,u1_struct_0(sK2))
      | ~ r1_orders_2(sK3,X22,X23)
      | ~ m1_subset_1(X23,u1_struct_0(X24))
      | ~ m1_subset_1(X22,u1_struct_0(X24))
      | ~ m1_subset_1(X22,u1_struct_0(sK3))
      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(u1_struct_0(X24),u1_orders_2(X24))
      | ~ l1_orders_2(X24)
      | r1_orders_2(X24,X22,X23) ) ),
    inference(forward_demodulation,[],[f3180,f3299])).

fof(f3180,plain,(
    ! [X24,X23,X22] :
      ( ~ r1_orders_2(sK3,X22,X23)
      | ~ m1_subset_1(X23,u1_struct_0(X24))
      | ~ m1_subset_1(X22,u1_struct_0(X24))
      | ~ m1_subset_1(X23,u1_struct_0(sK3))
      | ~ m1_subset_1(X22,u1_struct_0(sK3))
      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(u1_struct_0(X24),u1_orders_2(X24))
      | ~ l1_orders_2(X24)
      | r1_orders_2(X24,X22,X23) ) ),
    inference(resolution,[],[f3086,f3152])).

fof(f3152,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X4,X5) ) ),
    inference(equality_resolution,[],[f3151])).

fof(f3151,plain,(
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
    inference(equality_resolution,[],[f3137])).

fof(f3137,plain,(
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
    inference(cnf_transformation,[],[f3043])).

fof(f3043,plain,(
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
    inference(flattening,[],[f3042])).

fof(f3042,plain,(
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
    inference(ennf_transformation,[],[f2986])).

fof(f2986,axiom,(
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

fof(f10181,plain,
    ( r1_orders_2(sK3,k1_yellow_0(sK3,sK4),sK9(sK2,sK4,k1_yellow_0(sK3,sK4)))
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(subsumption_resolution,[],[f10164,f4512])).

fof(f10164,plain,
    ( ~ m1_subset_1(sK9(sK2,sK4,k1_yellow_0(sK3,sK4)),u1_struct_0(sK2))
    | r1_orders_2(sK3,k1_yellow_0(sK3,sK4),sK9(sK2,sK4,k1_yellow_0(sK3,sK4)))
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(resolution,[],[f10150,f3512])).

fof(f3512,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK3,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK3,k1_yellow_0(sK3,sK4),X0) ) ),
    inference(resolution,[],[f3505,f3428])).

fof(f3505,plain,(
    ! [X10,X11] :
      ( ~ r1_yellow_0(sK3,X10)
      | ~ r2_lattice3(sK3,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK2))
      | r1_orders_2(sK3,k1_yellow_0(sK3,X10),X11) ) ),
    inference(subsumption_resolution,[],[f3504,f3315])).

fof(f3504,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(k1_yellow_0(sK3,X10),u1_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(sK2))
      | ~ r2_lattice3(sK3,X10,X11)
      | ~ r1_yellow_0(sK3,X10)
      | r1_orders_2(sK3,k1_yellow_0(sK3,X10),X11) ) ),
    inference(forward_demodulation,[],[f3503,f3299])).

fof(f3503,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK2))
      | ~ r2_lattice3(sK3,X10,X11)
      | ~ r1_yellow_0(sK3,X10)
      | ~ m1_subset_1(k1_yellow_0(sK3,X10),u1_struct_0(sK3))
      | r1_orders_2(sK3,k1_yellow_0(sK3,X10),X11) ) ),
    inference(forward_demodulation,[],[f3175,f3299])).

fof(f3175,plain,(
    ! [X10,X11] :
      ( ~ r2_lattice3(sK3,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK3))
      | ~ r1_yellow_0(sK3,X10)
      | ~ m1_subset_1(k1_yellow_0(sK3,X10),u1_struct_0(sK3))
      | r1_orders_2(sK3,k1_yellow_0(sK3,X10),X11) ) ),
    inference(resolution,[],[f3086,f3145])).

fof(f3145,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X4) ) ),
    inference(equality_resolution,[],[f3092])).

fof(f3092,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3060])).

fof(f10150,plain,
    ( r2_lattice3(sK3,sK4,sK9(sK2,sK4,k1_yellow_0(sK3,sK4)))
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(subsumption_resolution,[],[f10149,f3089])).

fof(f10149,plain,
    ( k1_yellow_0(sK2,sK4) = k1_yellow_0(sK3,sK4)
    | r2_lattice3(sK3,sK4,sK9(sK2,sK4,k1_yellow_0(sK3,sK4)))
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(subsumption_resolution,[],[f10148,f4427])).

fof(f10148,plain,
    ( ~ r2_lattice3(sK2,sK4,k1_yellow_0(sK3,sK4))
    | k1_yellow_0(sK2,sK4) = k1_yellow_0(sK3,sK4)
    | r2_lattice3(sK3,sK4,sK9(sK2,sK4,k1_yellow_0(sK3,sK4)))
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(subsumption_resolution,[],[f10142,f3315])).

fof(f10142,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK2))
    | ~ r2_lattice3(sK2,sK4,k1_yellow_0(sK3,sK4))
    | k1_yellow_0(sK2,sK4) = k1_yellow_0(sK3,sK4)
    | r2_lattice3(sK3,sK4,sK9(sK2,sK4,k1_yellow_0(sK3,sK4)))
    | ~ spl15_18
    | ~ spl15_53 ),
    inference(resolution,[],[f7701,f4512])).

fof(f7701,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK9(sK2,sK4,X2),u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ r2_lattice3(sK2,sK4,X2)
        | k1_yellow_0(sK2,sK4) = X2
        | r2_lattice3(sK3,sK4,sK9(sK2,sK4,X2)) )
    | ~ spl15_18 ),
    inference(forward_demodulation,[],[f7700,f3299])).

fof(f7700,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(sK9(sK2,sK4,X2),u1_struct_0(sK3))
        | ~ r2_lattice3(sK2,sK4,X2)
        | k1_yellow_0(sK2,sK4) = X2
        | r2_lattice3(sK3,sK4,sK9(sK2,sK4,X2)) )
    | ~ spl15_18 ),
    inference(subsumption_resolution,[],[f7699,f3158])).

fof(f7699,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != k7_lattice3(k7_lattice3(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(sK9(sK2,sK4,X2),u1_struct_0(sK3))
        | ~ r2_lattice3(sK2,sK4,X2)
        | k1_yellow_0(sK2,sK4) = X2
        | r2_lattice3(sK3,sK4,sK9(sK2,sK4,X2)) )
    | ~ spl15_18 ),
    inference(forward_demodulation,[],[f7698,f3299])).

fof(f7698,plain,
    ( ! [X2] :
        ( k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(sK9(sK2,sK4,X2),u1_struct_0(sK3))
        | ~ r2_lattice3(sK2,sK4,X2)
        | k1_yellow_0(sK2,sK4) = X2
        | r2_lattice3(sK3,sK4,sK9(sK2,sK4,X2)) )
    | ~ spl15_18 ),
    inference(forward_demodulation,[],[f7692,f3379])).

fof(f7692,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK2))
        | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != k7_lattice3(k7_lattice3(sK2))
        | ~ m1_subset_1(sK9(sK2,sK4,X2),u1_struct_0(sK3))
        | ~ r2_lattice3(sK2,sK4,X2)
        | k1_yellow_0(sK2,sK4) = X2
        | r2_lattice3(sK3,sK4,sK9(sK2,sK4,X2)) )
    | ~ spl15_18 ),
    inference(resolution,[],[f7450,f3086])).

fof(f7450,plain,
    ( ! [X2,X3] :
        ( ~ l1_orders_2(X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ m1_subset_1(sK9(sK2,sK4,X2),u1_struct_0(X3))
        | ~ r2_lattice3(sK2,sK4,X2)
        | k1_yellow_0(sK2,sK4) = X2
        | r2_lattice3(X3,sK4,sK9(sK2,sK4,X2)) )
    | ~ spl15_18 ),
    inference(duplicate_literal_removal,[],[f7449])).

fof(f7449,plain,
    ( ! [X2,X3] :
        ( k1_yellow_0(sK2,sK4) = X2
        | k1_yellow_0(sK2,sK4) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ m1_subset_1(sK9(sK2,sK4,X2),u1_struct_0(X3))
        | ~ r2_lattice3(sK2,sK4,X2)
        | ~ l1_orders_2(X3)
        | r2_lattice3(X3,sK4,sK9(sK2,sK4,X2)) )
    | ~ spl15_18 ),
    inference(forward_demodulation,[],[f7448,f3739])).

fof(f7448,plain,
    ( ! [X2,X3] :
        ( k1_yellow_0(sK2,sK4) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ m1_subset_1(sK9(sK2,sK4,X2),u1_struct_0(X3))
        | ~ r2_lattice3(sK2,sK4,X2)
        | ~ l1_orders_2(X3)
        | r2_lattice3(X3,sK4,sK9(sK2,sK4,X2))
        | sK8(sK2,sK4) = X2 )
    | ~ spl15_18 ),
    inference(subsumption_resolution,[],[f7444,f3185])).

fof(f7444,plain,
    ( ! [X2,X3] :
        ( k1_yellow_0(sK2,sK4) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ m1_subset_1(sK9(sK2,sK4,X2),u1_struct_0(X3))
        | ~ r2_lattice3(sK2,sK4,X2)
        | ~ l1_orders_2(X3)
        | r2_lattice3(X3,sK4,sK9(sK2,sK4,X2))
        | sK8(sK2,sK4) = X2
        | ~ sP0(sK2,sK4) )
    | ~ spl15_18 ),
    inference(duplicate_literal_removal,[],[f7443])).

fof(f7443,plain,
    ( ! [X2,X3] :
        ( k1_yellow_0(sK2,sK4) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ m1_subset_1(sK9(sK2,sK4,X2),u1_struct_0(X3))
        | ~ r2_lattice3(sK2,sK4,X2)
        | ~ l1_orders_2(X3)
        | r2_lattice3(X3,sK4,sK9(sK2,sK4,X2))
        | sK8(sK2,sK4) = X2
        | ~ r2_lattice3(sK2,sK4,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ sP0(sK2,sK4) )
    | ~ spl15_18 ),
    inference(resolution,[],[f7426,f3101])).

fof(f3101,plain,(
    ! [X0,X7,X1] :
      ( m1_subset_1(sK9(X0,X1,X7),u1_struct_0(X0))
      | sK8(X0,X1) = X7
      | ~ r2_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3068])).

fof(f7426,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK9(sK2,sK4,X2),u1_struct_0(sK2))
        | k1_yellow_0(sK2,sK4) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ m1_subset_1(sK9(sK2,sK4,X2),u1_struct_0(X3))
        | ~ r2_lattice3(sK2,sK4,X2)
        | ~ l1_orders_2(X3)
        | r2_lattice3(X3,sK4,sK9(sK2,sK4,X2)) )
    | ~ spl15_18 ),
    inference(resolution,[],[f7396,f3549])).

fof(f3549,plain,(
    ! [X17,X18,X16] :
      ( ~ r2_lattice3(sK2,X16,X17)
      | k7_lattice3(k7_lattice3(sK2)) != g1_orders_2(u1_struct_0(X18),u1_orders_2(X18))
      | ~ m1_subset_1(X17,u1_struct_0(X18))
      | ~ m1_subset_1(X17,u1_struct_0(sK2))
      | ~ l1_orders_2(X18)
      | r2_lattice3(X18,X16,X17) ) ),
    inference(forward_demodulation,[],[f3164,f3158])).

fof(f3164,plain,(
    ! [X17,X18,X16] :
      ( ~ r2_lattice3(sK2,X16,X17)
      | ~ m1_subset_1(X17,u1_struct_0(X18))
      | ~ m1_subset_1(X17,u1_struct_0(sK2))
      | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X18),u1_orders_2(X18))
      | ~ l1_orders_2(X18)
      | r2_lattice3(X18,X16,X17) ) ),
    inference(resolution,[],[f3085,f3148])).

fof(f7396,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,sK4,sK9(sK2,sK4,X1))
        | ~ r2_lattice3(sK2,sK4,X1)
        | k1_yellow_0(sK2,sK4) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK2)) )
    | ~ spl15_18 ),
    inference(backward_demodulation,[],[f3188,f3739])).

fof(f3188,plain,(
    ! [X1] :
      ( ~ r2_lattice3(sK2,sK4,X1)
      | r2_lattice3(sK2,sK4,sK9(sK2,sK4,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sK8(sK2,sK4) = X1 ) ),
    inference(resolution,[],[f3185,f3102])).

fof(f3102,plain,(
    ! [X0,X7,X1] :
      ( ~ sP0(X0,X1)
      | r2_lattice3(X0,X1,sK9(X0,X1,X7))
      | ~ r2_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | sK8(X0,X1) = X7 ) ),
    inference(cnf_transformation,[],[f3068])).

fof(f7388,plain,
    ( spl15_18
    | spl15_19
    | ~ spl15_13 ),
    inference(avatar_split_clause,[],[f7387,f3486,f3741,f3737])).

fof(f3741,plain,
    ( spl15_19
  <=> r2_lattice3(sK2,sK4,sK5(sK2,sK4,sK8(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).

fof(f3486,plain,
    ( spl15_13
  <=> m1_subset_1(sK8(sK2,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).

fof(f7387,plain,
    ( r2_lattice3(sK2,sK4,sK5(sK2,sK4,sK8(sK2,sK4)))
    | k1_yellow_0(sK2,sK4) = sK8(sK2,sK4)
    | ~ spl15_13 ),
    inference(subsumption_resolution,[],[f7180,f3487])).

fof(f3487,plain,
    ( m1_subset_1(sK8(sK2,sK4),u1_struct_0(sK2))
    | ~ spl15_13 ),
    inference(avatar_component_clause,[],[f3486])).

fof(f7180,plain,
    ( r2_lattice3(sK2,sK4,sK5(sK2,sK4,sK8(sK2,sK4)))
    | ~ m1_subset_1(sK8(sK2,sK4),u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK4) = sK8(sK2,sK4) ),
    inference(resolution,[],[f3186,f3450])).

fof(f3450,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,sK4,X0)
      | r2_lattice3(sK2,sK4,sK5(sK2,sK4,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | k1_yellow_0(sK2,sK4) = X0 ) ),
    inference(resolution,[],[f3153,f3088])).

fof(f3153,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK2,X0)
      | ~ r2_lattice3(sK2,X0,X1)
      | r2_lattice3(sK2,X0,sK5(sK2,X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | k1_yellow_0(sK2,X0) = X1 ) ),
    inference(resolution,[],[f3085,f3094])).

fof(f3094,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3060])).

fof(f3186,plain,(
    r2_lattice3(sK2,sK4,sK8(sK2,sK4)) ),
    inference(resolution,[],[f3185,f3099])).

fof(f3099,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r2_lattice3(X0,X1,sK8(X0,X1)) ) ),
    inference(cnf_transformation,[],[f3068])).

fof(f7378,plain,
    ( ~ spl15_13
    | spl15_18
    | ~ spl15_210 ),
    inference(avatar_contradiction_clause,[],[f7377])).

fof(f7377,plain,
    ( $false
    | ~ spl15_13
    | spl15_18
    | ~ spl15_210 ),
    inference(subsumption_resolution,[],[f7376,f3738])).

fof(f3738,plain,
    ( k1_yellow_0(sK2,sK4) != sK8(sK2,sK4)
    | spl15_18 ),
    inference(avatar_component_clause,[],[f3737])).

fof(f7376,plain,
    ( k1_yellow_0(sK2,sK4) = sK8(sK2,sK4)
    | ~ spl15_13
    | ~ spl15_210 ),
    inference(subsumption_resolution,[],[f7375,f3487])).

fof(f7375,plain,
    ( ~ m1_subset_1(sK8(sK2,sK4),u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK4) = sK8(sK2,sK4)
    | ~ spl15_210 ),
    inference(subsumption_resolution,[],[f7374,f3088])).

fof(f7374,plain,
    ( ~ r1_yellow_0(sK2,sK4)
    | ~ m1_subset_1(sK8(sK2,sK4),u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK4) = sK8(sK2,sK4)
    | ~ spl15_210 ),
    inference(subsumption_resolution,[],[f7372,f3186])).

fof(f7372,plain,
    ( ~ r2_lattice3(sK2,sK4,sK8(sK2,sK4))
    | ~ r1_yellow_0(sK2,sK4)
    | ~ m1_subset_1(sK8(sK2,sK4),u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK4) = sK8(sK2,sK4)
    | ~ spl15_210 ),
    inference(resolution,[],[f6162,f3154])).

fof(f3154,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK2,X2,sK5(sK2,X3,X2))
      | ~ r2_lattice3(sK2,X3,X2)
      | ~ r1_yellow_0(sK2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | k1_yellow_0(sK2,X3) = X2 ) ),
    inference(resolution,[],[f3085,f3095])).

fof(f3095,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3060])).

fof(f6162,plain,
    ( r1_orders_2(sK2,sK8(sK2,sK4),sK5(sK2,sK4,sK8(sK2,sK4)))
    | ~ spl15_210 ),
    inference(avatar_component_clause,[],[f6160])).

fof(f6160,plain,
    ( spl15_210
  <=> r1_orders_2(sK2,sK8(sK2,sK4),sK5(sK2,sK4,sK8(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_210])])).

fof(f7258,plain,
    ( spl15_210
    | ~ spl15_208
    | ~ spl15_19 ),
    inference(avatar_split_clause,[],[f7248,f3741,f6151,f6160])).

fof(f6151,plain,
    ( spl15_208
  <=> m1_subset_1(sK5(sK2,sK4,sK8(sK2,sK4)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_208])])).

fof(f7248,plain,
    ( ~ m1_subset_1(sK5(sK2,sK4,sK8(sK2,sK4)),u1_struct_0(sK2))
    | r1_orders_2(sK2,sK8(sK2,sK4),sK5(sK2,sK4,sK8(sK2,sK4)))
    | ~ spl15_19 ),
    inference(resolution,[],[f3743,f3187])).

fof(f3187,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,sK8(sK2,sK4),X0) ) ),
    inference(resolution,[],[f3185,f3100])).

fof(f3100,plain,(
    ! [X0,X1,X9] :
      ( ~ sP0(X0,X1)
      | ~ r2_lattice3(X0,X1,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | r1_orders_2(X0,sK8(X0,X1),X9) ) ),
    inference(cnf_transformation,[],[f3068])).

fof(f3743,plain,
    ( r2_lattice3(sK2,sK4,sK5(sK2,sK4,sK8(sK2,sK4)))
    | ~ spl15_19 ),
    inference(avatar_component_clause,[],[f3741])).

fof(f6283,plain,
    ( ~ spl15_13
    | spl15_18
    | spl15_208 ),
    inference(avatar_contradiction_clause,[],[f6282])).

fof(f6282,plain,
    ( $false
    | ~ spl15_13
    | spl15_18
    | spl15_208 ),
    inference(subsumption_resolution,[],[f6281,f3085])).

fof(f6281,plain,
    ( ~ l1_orders_2(sK2)
    | ~ spl15_13
    | spl15_18
    | spl15_208 ),
    inference(subsumption_resolution,[],[f6280,f3487])).

fof(f6280,plain,
    ( ~ m1_subset_1(sK8(sK2,sK4),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | spl15_18
    | spl15_208 ),
    inference(subsumption_resolution,[],[f6279,f3088])).

fof(f6279,plain,
    ( ~ r1_yellow_0(sK2,sK4)
    | ~ m1_subset_1(sK8(sK2,sK4),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | spl15_18
    | spl15_208 ),
    inference(subsumption_resolution,[],[f6278,f3186])).

fof(f6278,plain,
    ( ~ r2_lattice3(sK2,sK4,sK8(sK2,sK4))
    | ~ r1_yellow_0(sK2,sK4)
    | ~ m1_subset_1(sK8(sK2,sK4),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | spl15_18
    | spl15_208 ),
    inference(subsumption_resolution,[],[f6277,f3738])).

fof(f6277,plain,
    ( k1_yellow_0(sK2,sK4) = sK8(sK2,sK4)
    | ~ r2_lattice3(sK2,sK4,sK8(sK2,sK4))
    | ~ r1_yellow_0(sK2,sK4)
    | ~ m1_subset_1(sK8(sK2,sK4),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | spl15_208 ),
    inference(resolution,[],[f6153,f3093])).

fof(f3093,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3060])).

fof(f6153,plain,
    ( ~ m1_subset_1(sK5(sK2,sK4,sK8(sK2,sK4)),u1_struct_0(sK2))
    | spl15_208 ),
    inference(avatar_component_clause,[],[f6151])).

fof(f4579,plain,
    ( ~ spl15_18
    | spl15_53 ),
    inference(avatar_contradiction_clause,[],[f4578])).

fof(f4578,plain,
    ( $false
    | ~ spl15_18
    | spl15_53 ),
    inference(subsumption_resolution,[],[f4577,f3089])).

fof(f4577,plain,
    ( k1_yellow_0(sK2,sK4) = k1_yellow_0(sK3,sK4)
    | ~ spl15_18
    | spl15_53 ),
    inference(forward_demodulation,[],[f4576,f3739])).

fof(f4576,plain,
    ( k1_yellow_0(sK3,sK4) = sK8(sK2,sK4)
    | spl15_53 ),
    inference(subsumption_resolution,[],[f4575,f3185])).

fof(f4575,plain,
    ( k1_yellow_0(sK3,sK4) = sK8(sK2,sK4)
    | ~ sP0(sK2,sK4)
    | spl15_53 ),
    inference(subsumption_resolution,[],[f4574,f3315])).

fof(f4574,plain,
    ( k1_yellow_0(sK3,sK4) = sK8(sK2,sK4)
    | ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK2))
    | ~ sP0(sK2,sK4)
    | spl15_53 ),
    inference(subsumption_resolution,[],[f4573,f4427])).

fof(f4573,plain,
    ( k1_yellow_0(sK3,sK4) = sK8(sK2,sK4)
    | ~ r2_lattice3(sK2,sK4,k1_yellow_0(sK3,sK4))
    | ~ m1_subset_1(k1_yellow_0(sK3,sK4),u1_struct_0(sK2))
    | ~ sP0(sK2,sK4)
    | spl15_53 ),
    inference(resolution,[],[f4513,f3101])).

fof(f4513,plain,
    ( ~ m1_subset_1(sK9(sK2,sK4,k1_yellow_0(sK3,sK4)),u1_struct_0(sK2))
    | spl15_53 ),
    inference(avatar_component_clause,[],[f4511])).

fof(f3502,plain,(
    spl15_13 ),
    inference(avatar_contradiction_clause,[],[f3501])).

fof(f3501,plain,
    ( $false
    | spl15_13 ),
    inference(subsumption_resolution,[],[f3500,f3185])).

fof(f3500,plain,
    ( ~ sP0(sK2,sK4)
    | spl15_13 ),
    inference(resolution,[],[f3488,f3098])).

fof(f3098,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3068])).

fof(f3488,plain,
    ( ~ m1_subset_1(sK8(sK2,sK4),u1_struct_0(sK2))
    | spl15_13 ),
    inference(avatar_component_clause,[],[f3486])).
%------------------------------------------------------------------------------
