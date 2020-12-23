%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1658+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:29 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 448 expanded)
%              Number of leaves         :    7 ( 144 expanded)
%              Depth                    :   26
%              Number of atoms          :  306 (2918 expanded)
%              Number of equality atoms :   20 ( 411 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4493,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4492,f3308])).

fof(f3308,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3283])).

fof(f3283,plain,
    ( k2_yellow_0(sK2,sK3) != k2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    & r2_yellow_0(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f3249,f3282,f3281])).

fof(f3281,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k4_waybel_0(X0,X1))
            & r2_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow_0(sK2,X1) != k2_yellow_0(sK2,k4_waybel_0(sK2,X1))
          & r2_yellow_0(sK2,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3282,plain,
    ( ? [X1] :
        ( k2_yellow_0(sK2,X1) != k2_yellow_0(sK2,k4_waybel_0(sK2,X1))
        & r2_yellow_0(sK2,X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( k2_yellow_0(sK2,sK3) != k2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
      & r2_yellow_0(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f3249,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k4_waybel_0(X0,X1))
          & r2_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3248])).

fof(f3248,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k4_waybel_0(X0,X1))
          & r2_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3232])).

fof(f3232,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_yellow_0(X0,X1)
             => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3231])).

fof(f3231,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_yellow_0(X0,X1)
           => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_0)).

fof(f4492,plain,(
    v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4491,f3309])).

fof(f3309,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3283])).

fof(f4491,plain,
    ( ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4490,f3310])).

fof(f3310,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3283])).

fof(f4490,plain,
    ( ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4489,f3311])).

fof(f3311,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3283])).

fof(f4489,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4488,f3312])).

fof(f3312,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f3283])).

fof(f4488,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4487,f3506])).

fof(f3506,plain,(
    m1_subset_1(sK7(sK2,sK3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f3505,f3308])).

fof(f3505,plain,
    ( m1_subset_1(sK7(sK2,sK3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3504,f3311])).

fof(f3504,plain,
    ( m1_subset_1(sK7(sK2,sK3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3498,f3313])).

fof(f3313,plain,(
    r2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f3283])).

fof(f3498,plain,
    ( m1_subset_1(sK7(sK2,sK3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f3364,f3370])).

fof(f3370,plain,(
    ! [X2,X0,X1] :
      ( sQ11_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f3338,f3363])).

fof(f3363,plain,(
    ! [X1,X0] :
      ( sQ11_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).

fof(f3338,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3298])).

fof(f3298,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ( ( ~ r1_lattice3(X0,X2,sK7(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK7(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK7(X0,X1,X2))
              | r1_lattice3(X0,X1,sK7(X0,X1,X2)) )
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3296,f3297])).

fof(f3297,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK7(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK7(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK7(X0,X1,X2))
          | r1_lattice3(X0,X1,sK7(X0,X1,X2)) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3296,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3295])).

fof(f3295,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3265])).

fof(f3265,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3264])).

fof(f3264,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3046])).

fof(f3046,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) )
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_yellow_0)).

fof(f3364,plain,(
    ~ sQ11_eqProxy(k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,k4_waybel_0(sK2,sK3))) ),
    inference(equality_proxy_replacement,[],[f3314,f3363])).

fof(f3314,plain,(
    k2_yellow_0(sK2,sK3) != k2_yellow_0(sK2,k4_waybel_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f3283])).

fof(f4487,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4472,f4477])).

fof(f4477,plain,(
    ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,sK3,k4_waybel_0(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f4476,f3308])).

fof(f4476,plain,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4475,f3311])).

fof(f4475,plain,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4474,f3313])).

fof(f4474,plain,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4467,f3364])).

fof(f4467,plain,
    ( sQ11_eqProxy(k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,k4_waybel_0(sK2,sK3)))
    | ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f4464,f3368])).

fof(f3368,plain,(
    ! [X2,X0,X1] :
      ( sQ11_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X2,sK7(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f3340,f3363])).

fof(f3340,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK7(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3298])).

fof(f4464,plain,(
    r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f4463,f3506])).

fof(f4463,plain,
    ( r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | ~ m1_subset_1(sK7(sK2,sK3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f4451])).

fof(f4451,plain,
    ( r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | ~ m1_subset_1(sK7(sK2,sK3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(resolution,[],[f3509,f3495])).

fof(f3495,plain,(
    ! [X1] :
      ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),X1)
      | r1_lattice3(sK2,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f3494,f3308])).

fof(f3494,plain,(
    ! [X1] :
      ( r1_lattice3(sK2,sK3,X1)
      | ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3493,f3309])).

fof(f3493,plain,(
    ! [X1] :
      ( r1_lattice3(sK2,sK3,X1)
      | ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3492,f3310])).

fof(f3492,plain,(
    ! [X1] :
      ( r1_lattice3(sK2,sK3,X1)
      | ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3478,f3311])).

fof(f3478,plain,(
    ! [X1] :
      ( r1_lattice3(sK2,sK3,X1)
      | ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3312,f3320])).

fof(f3320,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3284])).

fof(f3284,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattice3(X0,X1,X2)
                  | ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
                & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                  | ~ r1_lattice3(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3257])).

fof(f3257,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3256])).

fof(f3256,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3229])).

fof(f3229,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_waybel_0)).

fof(f3509,plain,
    ( r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f3508,f3308])).

fof(f3508,plain,
    ( r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3507,f3311])).

fof(f3507,plain,
    ( r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3499,f3313])).

fof(f3499,plain,
    ( r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f3364,f3369])).

fof(f3369,plain,(
    ! [X2,X0,X1] :
      ( sQ11_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
      | r1_lattice3(X0,X2,sK7(X0,X1,X2))
      | r1_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f3339,f3363])).

fof(f3339,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,sK7(X0,X1,X2))
      | r1_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3298])).

fof(f4472,plain,
    ( r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | ~ m1_subset_1(sK7(sK2,sK3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f4464,f3319])).

fof(f3319,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3284])).
%------------------------------------------------------------------------------
