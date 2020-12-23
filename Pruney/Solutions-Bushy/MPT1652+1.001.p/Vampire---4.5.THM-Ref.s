%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1652+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 (4822 expanded)
%              Number of leaves         :    6 (1254 expanded)
%              Depth                    :   42
%              Number of atoms          :  427 (38237 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f380,plain,(
    $false ),
    inference(global_subsumption,[],[f377,f379])).

fof(f379,plain,(
    r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f378,f259])).

fof(f259,plain,(
    ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f258,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
      | ~ r1_yellow_0(sK0,X0)
      | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f93,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

% (8031)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
fof(f15,plain,
    ( ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
      | ~ r1_yellow_0(sK0,sK1) )
    & ( r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
      | r1_yellow_0(sK0,sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14,f13])).

fof(f13,plain,
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
          ( ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,X1))
            | ~ r1_yellow_0(sK0,X1) )
          & ( r1_yellow_0(sK0,k3_waybel_0(sK0,X1))
            | r1_yellow_0(sK0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,X1))
          | ~ r1_yellow_0(sK0,X1) )
        & ( r1_yellow_0(sK0,k3_waybel_0(sK0,X1))
          | r1_yellow_0(sK0,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
        | ~ r1_yellow_0(sK0,sK1) )
      & ( r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
        | r1_yellow_0(sK0,sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_yellow_0(X0,X1)
          <~> r1_yellow_0(X0,k3_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_yellow_0(X0,X1)
          <~> r1_yellow_0(X0,k3_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r1_yellow_0(X0,X1)
            <=> r1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_yellow_0(X0,X1)
          <=> r1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_0)).

fof(f93,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
      | ~ r1_yellow_0(sK0,X0)
      | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f90,f24])).

fof(f24,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
      | ~ r1_yellow_0(sK0,X0)
      | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f27,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK2(X0,X1,X2))
              | r2_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK2(X0,X1,X2))
          | r2_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_yellow_0)).

fof(f27,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f258,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f257,f208])).

fof(f208,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f206,f27])).

fof(f206,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | r1_yellow_0(sK0,sK1)
    | ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | r1_yellow_0(sK0,sK1)
    | r1_yellow_0(sK0,sK1)
    | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f87,f110])).

fof(f110,plain,(
    ! [X2,X3] :
      ( ~ r2_lattice3(sK0,sK1,sK2(sK0,X2,X3))
      | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,X2,X3))
      | ~ r1_yellow_0(sK0,X2)
      | r1_yellow_0(sK0,X3) ) ),
    inference(resolution,[],[f76,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,X1)
      | r1_yellow_0(sK0,X0) ) ),
    inference(global_subsumption,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(sK0,X0)
      | ~ r1_yellow_0(sK0,X1)
      | m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f21,f30])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X0)
      | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f75,f21])).

fof(f75,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
      | ~ r2_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f74,f22])).

fof(f22,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
      | ~ r2_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f73,f23])).

fof(f23,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
      | ~ r2_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f71,f24])).

fof(f71,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
      | ~ r2_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f25,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_0)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X1] :
      ( r2_lattice3(sK0,X1,sK2(sK0,k3_waybel_0(sK0,sK1),X1))
      | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),X1))
      | r1_yellow_0(sK0,sK1)
      | r1_yellow_0(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f86,f21])).

fof(f86,plain,(
    ! [X1] :
      ( r1_yellow_0(sK0,sK1)
      | r1_yellow_0(sK0,X1)
      | r2_lattice3(sK0,X1,sK2(sK0,k3_waybel_0(sK0,sK1),X1))
      | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f82,f24])).

fof(f82,plain,(
    ! [X1] :
      ( r1_yellow_0(sK0,sK1)
      | r1_yellow_0(sK0,X1)
      | r2_lattice3(sK0,X1,sK2(sK0,k3_waybel_0(sK0,sK1),X1))
      | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),X1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f26,plain,
    ( r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f257,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f256,f21])).

fof(f256,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f255,f22])).

fof(f255,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f23])).

fof(f254,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f253,f24])).

fof(f253,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f250,f25])).

fof(f250,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f236,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f236,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f235,f27])).

fof(f235,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,k3_waybel_0(sK0,sK1),sK1)) ),
    inference(subsumption_resolution,[],[f234,f21])).

fof(f234,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f233,f24])).

fof(f233,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | r1_yellow_0(sK0,sK1)
    | ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,k3_waybel_0(sK0,sK1),sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f208,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f378,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | r1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f374,f270])).

fof(f270,plain,(
    r1_yellow_0(sK0,sK1) ),
    inference(global_subsumption,[],[f260])).

fof(f260,plain,(
    r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f259,f26])).

fof(f374,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | ~ r1_yellow_0(sK0,sK1)
    | r1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f363,f110])).

fof(f363,plain,(
    r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f362,f259])).

fof(f362,plain,
    ( r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f357])).

fof(f357,plain,
    ( r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | r1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f283,f273])).

fof(f273,plain,(
    ! [X1] :
      ( r2_lattice3(sK0,X1,sK2(sK0,sK1,X1))
      | r2_lattice3(sK0,sK1,sK2(sK0,sK1,X1))
      | r1_yellow_0(sK0,X1) ) ),
    inference(resolution,[],[f270,f39])).

fof(f39,plain,(
    ! [X2,X3] :
      ( ~ r1_yellow_0(sK0,X3)
      | r1_yellow_0(sK0,X2)
      | r2_lattice3(sK0,X2,sK2(sK0,X3,X2))
      | r2_lattice3(sK0,X3,sK2(sK0,X3,X2)) ) ),
    inference(global_subsumption,[],[f24,f34])).

fof(f34,plain,(
    ! [X2,X3] :
      ( r1_yellow_0(sK0,X2)
      | ~ r1_yellow_0(sK0,X3)
      | r2_lattice3(sK0,X2,sK2(sK0,X3,X2))
      | r2_lattice3(sK0,X3,sK2(sK0,X3,X2))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f21,f31])).

fof(f283,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,X0))
      | r1_yellow_0(sK0,X0)
      | r2_lattice3(sK0,sK1,sK2(sK0,sK1,X0)) ) ),
    inference(resolution,[],[f278,f80])).

fof(f80,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X1)
      | r2_lattice3(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f79,f21])).

fof(f79,plain,(
    ! [X1] :
      ( r2_lattice3(sK0,sK1,X1)
      | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f22])).

fof(f78,plain,(
    ! [X1] :
      ( r2_lattice3(sK0,sK1,X1)
      | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f77,f23])).

fof(f77,plain,(
    ! [X1] :
      ( r2_lattice3(sK0,sK1,X1)
      | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f72,f24])).

fof(f72,plain,(
    ! [X1] :
      ( r2_lattice3(sK0,sK1,X1)
      | ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f25,f29])).

fof(f278,plain,(
    ! [X2] :
      ( m1_subset_1(sK2(sK0,sK1,X2),u1_struct_0(sK0))
      | r1_yellow_0(sK0,X2) ) ),
    inference(subsumption_resolution,[],[f277,f21])).

fof(f277,plain,(
    ! [X2] :
      ( r1_yellow_0(sK0,X2)
      | m1_subset_1(sK2(sK0,sK1,X2),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f274,f24])).

fof(f274,plain,(
    ! [X2] :
      ( r1_yellow_0(sK0,X2)
      | m1_subset_1(sK2(sK0,sK1,X2),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f270,f30])).

fof(f377,plain,(
    ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f373,f259])).

fof(f373,plain,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1,k3_waybel_0(sK0,sK1)))
    | r1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f363,f272])).

fof(f272,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,X0))
      | ~ r2_lattice3(sK0,X0,sK2(sK0,sK1,X0))
      | r1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f270,f40])).

fof(f40,plain,(
    ! [X4,X5] :
      ( ~ r1_yellow_0(sK0,X5)
      | r1_yellow_0(sK0,X4)
      | ~ r2_lattice3(sK0,X4,sK2(sK0,X5,X4))
      | ~ r2_lattice3(sK0,X5,sK2(sK0,X5,X4)) ) ),
    inference(global_subsumption,[],[f24,f35])).

fof(f35,plain,(
    ! [X4,X5] :
      ( r1_yellow_0(sK0,X4)
      | ~ r1_yellow_0(sK0,X5)
      | ~ r2_lattice3(sK0,X4,sK2(sK0,X5,X4))
      | ~ r2_lattice3(sK0,X5,sK2(sK0,X5,X4))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f21,f32])).

%------------------------------------------------------------------------------
