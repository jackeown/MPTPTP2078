%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1653+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:28 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
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
fof(f4057,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4056,f3289])).

fof(f3289,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3264,plain,
    ( k1_yellow_0(sK2,sK3) != k1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    & r1_yellow_0(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f3240,f3263,f3262])).

fof(f3262,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_waybel_0(X0,X1))
            & r1_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_yellow_0(sK2,X1) != k1_yellow_0(sK2,k3_waybel_0(sK2,X1))
          & r1_yellow_0(sK2,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3263,plain,
    ( ? [X1] :
        ( k1_yellow_0(sK2,X1) != k1_yellow_0(sK2,k3_waybel_0(sK2,X1))
        & r1_yellow_0(sK2,X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( k1_yellow_0(sK2,sK3) != k1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
      & r1_yellow_0(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f3240,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_waybel_0(X0,X1))
          & r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3239])).

fof(f3239,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_waybel_0(X0,X1))
          & r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3222])).

fof(f3222,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r1_yellow_0(X0,X1)
             => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3221])).

fof(f3221,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_yellow_0(X0,X1)
           => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_0)).

fof(f4056,plain,(
    v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4055,f3290])).

fof(f3290,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3264])).

fof(f4055,plain,
    ( ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4054,f3291])).

fof(f3291,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3264])).

fof(f4054,plain,
    ( ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4053,f3292])).

fof(f3292,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3264])).

fof(f4053,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4052,f3293])).

fof(f3293,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f3264])).

fof(f4052,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4051,f3436])).

fof(f3436,plain,(
    m1_subset_1(sK7(sK2,sK3,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f3435,f3289])).

fof(f3435,plain,
    ( m1_subset_1(sK7(sK2,sK3,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3434,f3292])).

fof(f3434,plain,
    ( m1_subset_1(sK7(sK2,sK3,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3428,f3294])).

fof(f3294,plain,(
    r1_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3428,plain,
    ( m1_subset_1(sK7(sK2,sK3,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ r1_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f3332,f3336])).

fof(f3336,plain,(
    ! [X2,X0,X1] :
      ( sQ11_eqProxy(k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f3315,f3331])).

fof(f3331,plain,(
    ! [X1,X0] :
      ( sQ11_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).

fof(f3315,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3279])).

fof(f3279,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ( ( ~ r2_lattice3(X0,X2,sK7(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK7(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK7(X0,X1,X2))
              | r2_lattice3(X0,X1,sK7(X0,X1,X2)) )
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3277,f3278])).

fof(f3278,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK7(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK7(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK7(X0,X1,X2))
          | r2_lattice3(X0,X1,sK7(X0,X1,X2)) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3277,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3276])).

fof(f3276,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3252])).

fof(f3252,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3251])).

fof(f3251,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3044])).

fof(f3044,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) )
            & r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_yellow_0)).

fof(f3332,plain,(
    ~ sQ11_eqProxy(k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,k3_waybel_0(sK2,sK3))) ),
    inference(equality_proxy_replacement,[],[f3295,f3331])).

fof(f3295,plain,(
    k1_yellow_0(sK2,sK3) != k1_yellow_0(sK2,k3_waybel_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f3264])).

fof(f4051,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4036,f4041])).

fof(f4041,plain,(
    ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,sK3,k3_waybel_0(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f4040,f3289])).

fof(f4040,plain,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4039,f3292])).

fof(f4039,plain,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4038,f3294])).

fof(f4038,plain,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | ~ r1_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4031,f3332])).

fof(f4031,plain,
    ( sQ11_eqProxy(k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,k3_waybel_0(sK2,sK3)))
    | ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | ~ r1_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f4028,f3334])).

fof(f3334,plain,(
    ! [X2,X0,X1] :
      ( sQ11_eqProxy(k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r2_lattice3(X0,X2,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f3317,f3331])).

fof(f3317,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3279])).

fof(f4028,plain,(
    r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f4027,f3436])).

fof(f4027,plain,
    ( r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | ~ m1_subset_1(sK7(sK2,sK3,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f4015])).

fof(f4015,plain,
    ( r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | ~ m1_subset_1(sK7(sK2,sK3,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(resolution,[],[f3439,f3426])).

fof(f3426,plain,(
    ! [X3] :
      ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X3)
      | r2_lattice3(sK2,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f3425,f3289])).

fof(f3425,plain,(
    ! [X3] :
      ( r2_lattice3(sK2,sK3,X3)
      | ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3424,f3290])).

fof(f3424,plain,(
    ! [X3] :
      ( r2_lattice3(sK2,sK3,X3)
      | ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3423,f3291])).

fof(f3423,plain,(
    ! [X3] :
      ( r2_lattice3(sK2,sK3,X3)
      | ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3415,f3292])).

fof(f3415,plain,(
    ! [X3] :
      ( r2_lattice3(sK2,sK3,X3)
      | ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3293,f3299])).

fof(f3299,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3265])).

fof(f3265,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattice3(X0,X1,X2)
                  | ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
                & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                  | ~ r2_lattice3(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3246])).

fof(f3246,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3245])).

fof(f3245,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3219])).

fof(f3219,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_0)).

fof(f3439,plain,
    ( r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f3438,f3289])).

fof(f3438,plain,
    ( r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3437,f3292])).

fof(f3437,plain,
    ( r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f3429,f3294])).

fof(f3429,plain,
    ( r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | ~ r1_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f3332,f3335])).

fof(f3335,plain,(
    ! [X2,X0,X1] :
      ( sQ11_eqProxy(k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | r2_lattice3(X0,X2,sK7(X0,X1,X2))
      | r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f3316,f3331])).

fof(f3316,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,sK7(X0,X1,X2))
      | r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3279])).

fof(f4036,plain,
    ( r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | ~ m1_subset_1(sK7(sK2,sK3,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f4028,f3298])).

fof(f3298,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3265])).
%------------------------------------------------------------------------------
