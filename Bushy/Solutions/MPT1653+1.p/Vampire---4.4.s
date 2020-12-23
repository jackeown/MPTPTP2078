%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t33_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:48 EDT 2019

% Result     : Theorem 36.62s
% Output     : Refutation 36.62s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 114 expanded)
%              Number of leaves         :    6 (  31 expanded)
%              Depth                    :   19
%              Number of atoms          :  293 ( 836 expanded)
%              Number of equality atoms :   28 ( 101 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1319,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1318,f224])).

fof(f224,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f177])).

fof(f177,plain,
    ( k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    & r1_yellow_0(sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f90,f176,f175])).

fof(f175,plain,
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
          ( k1_yellow_0(sK0,X1) != k1_yellow_0(sK0,k3_waybel_0(sK0,X1))
          & r1_yellow_0(sK0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f176,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_waybel_0(X0,X1))
          & r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_yellow_0(X0,sK1) != k1_yellow_0(X0,k3_waybel_0(X0,sK1))
        & r1_yellow_0(X0,sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_waybel_0(X0,X1))
          & r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_waybel_0(X0,X1))
          & r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r1_yellow_0(X0,X1)
             => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_yellow_0(X0,X1)
           => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t33_waybel_0.p',t33_waybel_0)).

fof(f1318,plain,(
    ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1317,f225])).

fof(f225,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f177])).

fof(f1317,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1316,f227])).

fof(f227,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f177])).

fof(f1316,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1315,f228])).

fof(f228,plain,(
    r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f177])).

fof(f1315,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1314,f223])).

fof(f223,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f177])).

fof(f1314,plain,
    ( v2_struct_0(sK0)
    | ~ r1_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1313,f226])).

fof(f226,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f177])).

fof(f1313,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ r1_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(trivial_inequality_removal,[],[f1310])).

fof(f1310,plain,
    ( k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ r1_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(superposition,[],[f229,f891])).

fof(f891,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f887,f532])).

fof(f532,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,sK9(X0,X1,k3_waybel_0(X0,X2)))
      | ~ r2_lattice3(X0,X1,sK9(X0,X1,k3_waybel_0(X0,X2)))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f531,f287])).

fof(f287,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f196,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ( ( ~ r2_lattice3(X0,X2,sK9(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK9(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK9(X0,X1,X2))
              | r2_lattice3(X0,X1,sK9(X0,X1,X2)) )
            & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f194,f195])).

fof(f195,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK9(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK9(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK9(X0,X1,X2))
          | r2_lattice3(X0,X1,sK9(X0,X1,X2)) )
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f194,plain,(
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
    inference(flattening,[],[f193])).

fof(f193,plain,(
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
    inference(nnf_transformation,[],[f146])).

fof(f146,plain,(
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
    inference(flattening,[],[f145])).

fof(f145,plain,(
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
    inference(ennf_transformation,[],[f72])).

fof(f72,axiom,(
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
    file('/export/starexec/sandbox/benchmark/waybel_0__t33_waybel_0.p',t47_yellow_0)).

fof(f531,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X2))
      | ~ r2_lattice3(X0,X1,sK9(X0,X1,k3_waybel_0(X0,X2)))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r2_lattice3(X0,X2,sK9(X0,X1,k3_waybel_0(X0,X2)))
      | ~ m1_subset_1(sK9(X0,X1,k3_waybel_0(X0,X2)),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f528])).

fof(f528,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X2))
      | ~ r2_lattice3(X0,X1,sK9(X0,X1,k3_waybel_0(X0,X2)))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r2_lattice3(X0,X2,sK9(X0,X1,k3_waybel_0(X0,X2)))
      | ~ m1_subset_1(sK9(X0,X1,k3_waybel_0(X0,X2)),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f289,f278])).

fof(f278,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f188,plain,(
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
    inference(nnf_transformation,[],[f140])).

fof(f140,plain,(
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
    inference(flattening,[],[f139])).

fof(f139,plain,(
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
    inference(ennf_transformation,[],[f70])).

fof(f70,axiom,(
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
    file('/export/starexec/sandbox/benchmark/waybel_0__t33_waybel_0.p',t31_waybel_0)).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,sK9(X0,X1,X2))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f887,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK9(X0,X1,k3_waybel_0(X0,X1)))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(factoring,[],[f526])).

fof(f526,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,sK9(X0,X1,k3_waybel_0(X0,X2)))
      | r2_lattice3(X0,X1,sK9(X0,X1,k3_waybel_0(X0,X2)))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f525,f287])).

fof(f525,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X2))
      | r2_lattice3(X0,X1,sK9(X0,X1,k3_waybel_0(X0,X2)))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X0,X2,sK9(X0,X1,k3_waybel_0(X0,X2)))
      | ~ m1_subset_1(sK9(X0,X1,k3_waybel_0(X0,X2)),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f523])).

fof(f523,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X2))
      | r2_lattice3(X0,X1,sK9(X0,X1,k3_waybel_0(X0,X2)))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X0,X2,sK9(X0,X1,k3_waybel_0(X0,X2)))
      | ~ m1_subset_1(sK9(X0,X1,k3_waybel_0(X0,X2)),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f288,f279])).

fof(f279,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,sK9(X0,X1,X2))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | r2_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f229,plain,(
    k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f177])).
%------------------------------------------------------------------------------
