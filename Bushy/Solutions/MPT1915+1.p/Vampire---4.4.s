%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t13_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:54 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  79 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  171 ( 425 expanded)
%              Number of equality atoms :   39 (  94 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f87,f139,f193,f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t13_yellow_6.p',free_g1_orders_2)).

fof(f193,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(k3_yellow_6(sK0,sK1,sK2)),u1_orders_2(k3_yellow_6(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f83,f84,f85,f86,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2)))
      | ~ l1_orders_2(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(global_subsumption,[],[f89,f88,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2)))
      | ~ l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
      | k3_yellow_6(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X1)
      | ~ v6_waybel_0(X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_yellow_6(X0,X1,X2) = X3
                      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                    & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                        & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                      | k3_yellow_6(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_yellow_6(X0,X1,X2) = X3
                      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                    & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                        & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                      | k3_yellow_6(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X1)
                    & v6_waybel_0(X3,X1) )
                 => ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t13_yellow_6.p',d7_yellow_6)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0) )
     => ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t13_yellow_6.p',dt_k3_yellow_6)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f70,f69,f68])).

fof(f68,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,sK1,X2))
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & l1_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,sK2))
        & m1_subset_1(sK2,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => u1_struct_0(X0) = u1_struct_0(k3_yellow_6(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(X0) = u1_struct_0(k3_yellow_6(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t13_yellow_6.p',t13_yellow_6)).

fof(f85,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f84,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f83,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f139,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f83,f112])).

fof(f112,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t13_yellow_6.p',dt_u1_orders_2)).

fof(f87,plain,(
    u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------
