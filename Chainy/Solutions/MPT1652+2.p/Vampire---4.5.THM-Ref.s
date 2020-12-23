%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1652+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.97s
% Output     : Refutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   89 (3613 expanded)
%              Number of leaves         :    6 ( 934 expanded)
%              Depth                    :   45
%              Number of atoms          :  445 (28642 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4383,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4382,f4143])).

fof(f4143,plain,(
    r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f4142,f3290])).

fof(f3290,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3264,plain,
    ( ( ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
      | ~ r1_yellow_0(sK2,sK3) )
    & ( r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
      | r1_yellow_0(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f3261,f3263,f3262])).

fof(f3262,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_yellow_0(X0,k3_waybel_0(X0,X1))
              | ~ r1_yellow_0(X0,X1) )
            & ( r1_yellow_0(X0,k3_waybel_0(X0,X1))
              | r1_yellow_0(X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ r1_yellow_0(sK2,k3_waybel_0(sK2,X1))
            | ~ r1_yellow_0(sK2,X1) )
          & ( r1_yellow_0(sK2,k3_waybel_0(sK2,X1))
            | r1_yellow_0(sK2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3263,plain,
    ( ? [X1] :
        ( ( ~ r1_yellow_0(sK2,k3_waybel_0(sK2,X1))
          | ~ r1_yellow_0(sK2,X1) )
        & ( r1_yellow_0(sK2,k3_waybel_0(sK2,X1))
          | r1_yellow_0(sK2,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
        | ~ r1_yellow_0(sK2,sK3) )
      & ( r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
        | r1_yellow_0(sK2,sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f3261,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_yellow_0(X0,k3_waybel_0(X0,X1))
            | ~ r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,k3_waybel_0(X0,X1))
            | r1_yellow_0(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3260])).

fof(f3260,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_yellow_0(X0,k3_waybel_0(X0,X1))
            | ~ r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,k3_waybel_0(X0,X1))
            | r1_yellow_0(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3237])).

fof(f3237,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_yellow_0(X0,X1)
          <~> r1_yellow_0(X0,k3_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3236])).

fof(f3236,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_yellow_0(X0,X1)
          <~> r1_yellow_0(X0,k3_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3221])).

fof(f3221,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r1_yellow_0(X0,X1)
            <=> r1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3220])).

fof(f3220,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_yellow_0(X0,X1)
          <=> r1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_0)).

fof(f4142,plain,
    ( r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4141,f3293])).

fof(f3293,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3264])).

fof(f4141,plain,
    ( r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4140,f4073])).

fof(f4073,plain,(
    ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4072,f3296])).

fof(f3296,plain,
    ( ~ r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f3264])).

fof(f4072,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4071,f3290])).

fof(f4071,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4070,f3293])).

fof(f4070,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f4069])).

fof(f4069,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | r1_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f4055,f3313])).

fof(f3313,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3277,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK7(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK7(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK7(X0,X1,X2))
              | r2_lattice3(X0,X1,sK7(X0,X1,X2)) )
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3275,f3276])).

fof(f3276,plain,(
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

fof(f3275,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3274])).

fof(f3274,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3250])).

fof(f3250,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3249])).

fof(f3249,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3043])).

fof(f3043,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) ) )
         => r1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_yellow_0)).

fof(f4055,plain,
    ( ~ m1_subset_1(sK7(sK2,k3_waybel_0(sK2,sK3),sK3),u1_struct_0(sK2))
    | r1_yellow_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f4053,f3991])).

fof(f3991,plain,
    ( r2_lattice3(sK2,sK3,sK7(sK2,k3_waybel_0(sK2,sK3),sK3))
    | r1_yellow_0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f3990])).

fof(f3990,plain,
    ( r2_lattice3(sK2,sK3,sK7(sK2,k3_waybel_0(sK2,sK3),sK3))
    | r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,sK3) ),
    inference(factoring,[],[f3938])).

fof(f3938,plain,(
    ! [X0] :
      ( r2_lattice3(sK2,X0,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | r2_lattice3(sK2,sK3,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,sK3) ) ),
    inference(resolution,[],[f3786,f3295])).

fof(f3295,plain,
    ( r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | r1_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3786,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
      | r2_lattice3(sK2,X0,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | r2_lattice3(sK2,sK3,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | r1_yellow_0(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f3785,f3296])).

fof(f3785,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,sK3)
      | r2_lattice3(sK2,X0,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | r2_lattice3(sK2,sK3,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f3784,f3290])).

fof(f3784,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,sK3)
      | r2_lattice3(sK2,X0,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | r2_lattice3(sK2,sK3,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3783,f3293])).

fof(f3783,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,sK3)
      | r2_lattice3(sK2,X0,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | r2_lattice3(sK2,sK3,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f3782])).

fof(f3782,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,sK3)
      | r2_lattice3(sK2,X0,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | r2_lattice3(sK2,sK3,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
      | r1_yellow_0(sK2,X0)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3560,f3313])).

fof(f3560,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK7(sK2,k3_waybel_0(sK2,sK3),X1),u1_struct_0(sK2))
      | r1_yellow_0(sK2,X1)
      | r1_yellow_0(sK2,sK3)
      | r2_lattice3(sK2,X1,sK7(sK2,k3_waybel_0(sK2,sK3),X1))
      | r2_lattice3(sK2,sK3,sK7(sK2,k3_waybel_0(sK2,sK3),X1)) ) ),
    inference(resolution,[],[f3373,f3419])).

fof(f3419,plain,(
    ! [X2] :
      ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r2_lattice3(sK2,sK3,X2) ) ),
    inference(resolution,[],[f3405,f3294])).

fof(f3294,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3405,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,k3_waybel_0(sK2,X0),X1)
      | r2_lattice3(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f3404,f3290])).

fof(f3404,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r2_lattice3(sK2,X0,X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3403,f3291])).

fof(f3291,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3403,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r2_lattice3(sK2,X0,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3402,f3293])).

fof(f3402,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | r2_lattice3(sK2,X0,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3301,f3292])).

fof(f3292,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3301,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2)
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
    inference(nnf_transformation,[],[f3245])).

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
    inference(flattening,[],[f3244])).

fof(f3244,plain,(
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

fof(f3373,plain,(
    ! [X0] :
      ( r2_lattice3(sK2,X0,sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,k3_waybel_0(sK2,sK3),X0))
      | r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,sK3) ) ),
    inference(resolution,[],[f3372,f3295])).

fof(f3372,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK2,X0)
      | r2_lattice3(sK2,X1,sK7(sK2,X0,X1))
      | r2_lattice3(sK2,X0,sK7(sK2,X0,X1))
      | r1_yellow_0(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f3370,f3290])).

fof(f3370,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK2,X0)
      | r2_lattice3(sK2,X1,sK7(sK2,X0,X1))
      | r2_lattice3(sK2,X0,sK7(sK2,X0,X1))
      | r1_yellow_0(sK2,X1)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3314,f3293])).

fof(f3314,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X2,sK7(X0,X1,X2))
      | r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | r1_yellow_0(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3277])).

fof(f4053,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r2_lattice3(sK2,sK3,sK7(sK2,k3_waybel_0(sK2,sK3),sK3))
    | ~ m1_subset_1(sK7(sK2,k3_waybel_0(sK2,sK3),sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f4045,f3399])).

fof(f3399,plain,(
    ! [X2] :
      ( r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X2)
      | ~ r2_lattice3(sK2,sK3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f3397,f3294])).

fof(f3397,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,X0,X1)
      | r2_lattice3(sK2,k3_waybel_0(sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f3396,f3290])).

fof(f3396,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r2_lattice3(sK2,k3_waybel_0(sK2,X0),X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3395,f3291])).

fof(f3395,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r2_lattice3(sK2,k3_waybel_0(sK2,X0),X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3394,f3293])).

fof(f3394,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | r2_lattice3(sK2,k3_waybel_0(sK2,X0),X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3300,f3292])).

fof(f3300,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3265])).

fof(f4045,plain,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,k3_waybel_0(sK2,sK3),sK3))
    | r1_yellow_0(sK2,sK3) ),
    inference(resolution,[],[f4033,f3295])).

fof(f4033,plain,
    ( ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,k3_waybel_0(sK2,sK3),sK3)) ),
    inference(subsumption_resolution,[],[f4032,f3296])).

fof(f4032,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,k3_waybel_0(sK2,sK3),sK3)) ),
    inference(subsumption_resolution,[],[f4031,f3290])).

fof(f4031,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,k3_waybel_0(sK2,sK3),sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4030,f3293])).

fof(f4030,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,k3_waybel_0(sK2,sK3),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f4017])).

fof(f4017,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | r1_yellow_0(sK2,sK3)
    | ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK7(sK2,k3_waybel_0(sK2,sK3),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f3991,f3315])).

fof(f3315,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,sK7(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3277])).

fof(f4140,plain,
    ( r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4139,f4075])).

fof(f4075,plain,(
    r1_yellow_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3295,f4073])).

fof(f4139,plain,
    ( r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | ~ r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f4136,f3313])).

fof(f4136,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f4131,f4073])).

fof(f4131,plain,
    ( r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f4083])).

fof(f4083,plain,
    ( r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3))) ),
    inference(resolution,[],[f4080,f3419])).

fof(f4080,plain,(
    ! [X2] :
      ( r2_lattice3(sK2,X2,sK7(sK2,sK3,X2))
      | r2_lattice3(sK2,sK3,sK7(sK2,sK3,X2))
      | r1_yellow_0(sK2,X2) ) ),
    inference(resolution,[],[f4075,f3372])).

fof(f4382,plain,(
    ~ r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3))) ),
    inference(duplicate_literal_removal,[],[f4380])).

fof(f4380,plain,
    ( ~ r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3)))
    | ~ r2_lattice3(sK2,sK3,sK7(sK2,sK3,k3_waybel_0(sK2,sK3))) ),
    inference(resolution,[],[f4210,f4075])).

fof(f4210,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK2,X0)
      | ~ r2_lattice3(sK2,sK3,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | ~ r2_lattice3(sK2,X0,sK7(sK2,X0,k3_waybel_0(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f4209,f3290])).

fof(f4209,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,sK3,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | ~ r1_yellow_0(sK2,X0)
      | ~ r2_lattice3(sK2,X0,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f4208,f3293])).

fof(f4208,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,sK3,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | ~ r1_yellow_0(sK2,X0)
      | ~ r2_lattice3(sK2,X0,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f4207,f4073])).

fof(f4207,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,sK3,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | ~ r1_yellow_0(sK2,X0)
      | ~ r2_lattice3(sK2,X0,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f4206])).

fof(f4206,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,sK3,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | ~ r1_yellow_0(sK2,X0)
      | ~ r2_lattice3(sK2,X0,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | ~ r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f4074,f3313])).

fof(f4074,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(sK2,X0,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
      | ~ r2_lattice3(sK2,sK3,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | ~ r1_yellow_0(sK2,X0)
      | ~ r2_lattice3(sK2,X0,sK7(sK2,X0,k3_waybel_0(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f3413,f4073])).

fof(f3413,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,sK3,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | ~ m1_subset_1(sK7(sK2,X0,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
      | ~ r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
      | ~ r2_lattice3(sK2,X0,sK7(sK2,X0,k3_waybel_0(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f3412,f3290])).

fof(f3412,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,sK3,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | ~ m1_subset_1(sK7(sK2,X0,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
      | ~ r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
      | ~ r2_lattice3(sK2,X0,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3407,f3293])).

fof(f3407,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,sK3,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | ~ m1_subset_1(sK7(sK2,X0,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
      | ~ r1_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,k3_waybel_0(sK2,sK3))
      | ~ r2_lattice3(sK2,X0,sK7(sK2,X0,k3_waybel_0(sK2,sK3)))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3399,f3315])).
%------------------------------------------------------------------------------
