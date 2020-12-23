%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t48_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:51 EDT 2019

% Result     : Theorem 157.66s
% Output     : Refutation 157.66s
% Verified   : 
% Statistics : Number of formulae       :  152 (3425 expanded)
%              Number of leaves         :   25 (1082 expanded)
%              Depth                    :   26
%              Number of atoms          :  861 (39354 expanded)
%              Number of equality atoms :   35 (5084 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126709,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f187,f194,f530,f2902,f126682])).

fof(f126682,plain,
    ( ~ spl11_0
    | ~ spl11_18 ),
    inference(avatar_contradiction_clause,[],[f126681])).

fof(f126681,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f126497,f126594])).

fof(f126594,plain,
    ( ~ r1_orders_2(sK0,sK8(k5_waybel_0(sK0,sK6(sK0,sK1)),sK1),sK6(sK0,sK1))
    | ~ spl11_0
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f2920,f112,f115,f195,f124952,f124949,f2409])).

fof(f2409,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v12_waybel_0(X3,X0)
      | r2_hidden(X1,X3)
      | ~ l1_orders_2(X0)
      | ~ r1_tarski(X3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f2392,f756])).

fof(f756,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f159,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t48_waybel_0.p',t3_subset)).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t48_waybel_0.p',t4_subset)).

fof(f2392,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v12_waybel_0(X3,X0)
      | r2_hidden(X1,X3)
      | ~ l1_orders_2(X0)
      | ~ r1_tarski(X3,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f121,f153])).

fof(f121,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | r2_hidden(X5,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK4(X0,X1),X1)
                & r1_orders_2(X0,sK4(X0,X1),sK3(X0,X1))
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f82,f84,f83])).

fof(f83,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X3,X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,X3,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,X2)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r1_orders_2(X0,sK4(X0,X1),X2)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t48_waybel_0.p',d19_waybel_0)).

fof(f124949,plain,
    ( m1_subset_1(sK8(k5_waybel_0(sK0,sK6(sK0,sK1)),sK1),u1_struct_0(sK0))
    | ~ spl11_0
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f109,f112,f2919,f124842,f7455])).

fof(f7455,plain,(
    ! [X14,X12,X13] :
      ( m1_subset_1(sK8(k5_waybel_0(X12,X13),X14),u1_struct_0(X12))
      | v2_struct_0(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | r1_tarski(k5_waybel_0(X12,X13),X14) ) ),
    inference(resolution,[],[f1288,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f100,f101])).

fof(f101,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t48_waybel_0.p',d3_tarski)).

fof(f1288,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k5_waybel_0(X3,X2))
      | ~ l1_orders_2(X3)
      | v2_struct_0(X3)
      | m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X2,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f142,f159])).

fof(f142,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t48_waybel_0.p',dt_k5_waybel_0)).

fof(f124842,plain,
    ( ~ r1_tarski(k5_waybel_0(sK0,sK6(sK0,sK1)),sK1)
    | ~ spl11_0
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f2994,f124839,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t48_waybel_0.p',d10_xboole_0)).

fof(f124839,plain,
    ( r1_tarski(sK1,k5_waybel_0(sK0,sK6(sK0,sK1)))
    | ~ spl11_0 ),
    inference(duplicate_literal_removal,[],[f124836])).

fof(f124836,plain,
    ( r1_tarski(sK1,k5_waybel_0(sK0,sK6(sK0,sK1)))
    | r1_tarski(sK1,k5_waybel_0(sK0,sK6(sK0,sK1)))
    | ~ spl11_0 ),
    inference(resolution,[],[f11634,f150])).

fof(f11634,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(X0,k5_waybel_0(sK0,sK6(sK0,sK1))),sK1)
        | r1_tarski(X0,k5_waybel_0(sK0,sK6(sK0,sK1))) )
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f11633,f1399])).

fof(f1399,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f116,f159])).

fof(f116,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,
    ( ( ! [X2] :
          ( k5_waybel_0(sK0,X2) != sK1
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      | ~ v14_waybel_0(sK1,sK0) )
    & ( ( k5_waybel_0(sK0,sK2) = sK1
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | v14_waybel_0(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v12_waybel_0(sK1,sK0)
    & v1_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f76,f79,f78,f77])).

fof(f77,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ! [X2] :
                  ( k5_waybel_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v14_waybel_0(X1,X0) )
            & ( ? [X3] :
                  ( k5_waybel_0(X0,X3) = X1
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | v14_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(sK0,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ v14_waybel_0(X1,sK0) )
          & ( ? [X3] :
                ( k5_waybel_0(sK0,X3) = X1
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            | v14_waybel_0(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v12_waybel_0(X1,sK0)
          & v1_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(X0,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v14_waybel_0(X1,X0) )
          & ( ? [X3] :
                ( k5_waybel_0(X0,X3) = X1
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | v14_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( ! [X2] :
              ( k5_waybel_0(X0,X2) != sK1
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v14_waybel_0(sK1,X0) )
        & ( ? [X3] :
              ( k5_waybel_0(X0,X3) = sK1
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | v14_waybel_0(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK1,X0)
        & v1_waybel_0(sK1,X0)
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ? [X3] :
          ( k5_waybel_0(X0,X3) = X1
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k5_waybel_0(X0,sK2) = X1
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(X0,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v14_waybel_0(X1,X0) )
          & ( ? [X3] :
                ( k5_waybel_0(X0,X3) = X1
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | v14_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(X0,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v14_waybel_0(X1,X0) )
          & ( ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | v14_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(X0,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v14_waybel_0(X1,X0) )
          & ( ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | v14_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v14_waybel_0(X1,X0)
          <~> ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v14_waybel_0(X1,X0)
          <~> ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
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
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v14_waybel_0(X1,X0)
            <=> ? [X2] :
                  ( k5_waybel_0(X0,X2) = X1
                  & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v14_waybel_0(X1,X0)
          <=> ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t48_waybel_0.p',t48_waybel_0)).

fof(f11633,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(X0,k5_waybel_0(sK0,sK6(sK0,sK1))),u1_struct_0(sK0))
        | r1_tarski(X0,k5_waybel_0(sK0,sK6(sK0,sK1)))
        | ~ r2_hidden(sK8(X0,k5_waybel_0(sK0,sK6(sK0,sK1))),sK1) )
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f11632,f109])).

fof(f11632,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(X0,k5_waybel_0(sK0,sK6(sK0,sK1))),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r1_tarski(X0,k5_waybel_0(sK0,sK6(sK0,sK1)))
        | ~ r2_hidden(sK8(X0,k5_waybel_0(sK0,sK6(sK0,sK1))),sK1) )
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f11631,f112])).

fof(f11631,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(X0,k5_waybel_0(sK0,sK6(sK0,sK1))),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | r1_tarski(X0,k5_waybel_0(sK0,sK6(sK0,sK1)))
        | ~ r2_hidden(sK8(X0,k5_waybel_0(sK0,sK6(sK0,sK1))),sK1) )
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f11629,f2919])).

fof(f11629,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(X0,k5_waybel_0(sK0,sK6(sK0,sK1))),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | r1_tarski(X0,k5_waybel_0(sK0,sK6(sK0,sK1)))
        | ~ r2_hidden(sK8(X0,k5_waybel_0(sK0,sK6(sK0,sK1))),sK1) )
    | ~ spl11_0 ),
    inference(resolution,[],[f2135,f2956])).

fof(f2956,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK6(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f2955,f1399])).

fof(f2955,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK6(sK0,sK1)) )
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f2954,f112])).

fof(f2954,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK6(sK0,sK1))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f2953,f2919])).

fof(f2953,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK6(sK0,sK1))
        | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_0 ),
    inference(resolution,[],[f2918,f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f87,f88])).

fof(f88,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
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
    inference(rectify,[],[f86])).

fof(f86,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t48_waybel_0.p',d9_lattice3)).

fof(f2918,plain,
    ( r2_lattice3(sK0,sK1,sK6(sK0,sK1))
    | ~ spl11_0 ),
    inference(unit_resulting_resolution,[],[f109,f110,f111,f112,f113,f114,f115,f116,f180,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK6(X0,X1))
      | ~ v14_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_waybel_0(X1,X0)
              | ! [X2] :
                  ( ~ r2_lattice3(X0,X1,X2)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ( r2_lattice3(X0,X1,sK6(X0,X1))
                & r2_hidden(sK6(X0,X1),X1)
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
              | ~ v14_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f91,f92])).

fof(f92,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_lattice3(X0,X1,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( r2_lattice3(X0,X1,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_waybel_0(X1,X0)
              | ! [X2] :
                  ( ~ r2_lattice3(X0,X1,X2)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ? [X3] :
                  ( r2_lattice3(X0,X1,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ v14_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_waybel_0(X1,X0)
              | ! [X2] :
                  ( ~ r2_lattice3(X0,X1,X2)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ? [X2] :
                  ( r2_lattice3(X0,X1,X2)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v14_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v14_waybel_0(X1,X0)
          <=> ? [X2] :
                ( r2_lattice3(X0,X1,X2)
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v14_waybel_0(X1,X0)
          <=> ? [X2] :
                ( r2_lattice3(X0,X1,X2)
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v14_waybel_0(X1,X0)
          <=> ? [X2] :
                ( r2_lattice3(X0,X1,X2)
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t48_waybel_0.p',d21_waybel_0)).

fof(f180,plain,
    ( v14_waybel_0(sK1,sK0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl11_0
  <=> v14_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f114,plain,(
    v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f113,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

fof(f111,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f110,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f2135,plain,(
    ! [X21,X19,X20] :
      ( ~ r1_orders_2(X19,sK8(X20,k5_waybel_0(X19,X21)),X21)
      | ~ m1_subset_1(sK8(X20,k5_waybel_0(X19,X21)),u1_struct_0(X19))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | ~ l1_orders_2(X19)
      | v2_struct_0(X19)
      | r1_tarski(X20,k5_waybel_0(X19,X21)) ) ),
    inference(resolution,[],[f137,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t48_waybel_0.p',t17_waybel_0)).

fof(f2994,plain,
    ( k5_waybel_0(sK0,sK6(sK0,sK1)) != sK1
    | ~ spl11_0
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f2919,f529])).

fof(f529,plain,
    ( ! [X2] :
        ( k5_waybel_0(sK0,X2) != sK1
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl11_18
  <=> ! [X2] :
        ( k5_waybel_0(sK0,X2) != sK1
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f2919,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_0 ),
    inference(unit_resulting_resolution,[],[f109,f110,f111,f112,f113,f114,f115,f116,f180,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ v14_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f109,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f124952,plain,
    ( ~ r2_hidden(sK8(k5_waybel_0(sK0,sK6(sK0,sK1)),sK1),sK1)
    | ~ spl11_0
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f124842,f151])).

fof(f195,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f116,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f115,plain,(
    v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f112,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f2920,plain,
    ( r2_hidden(sK6(sK0,sK1),sK1)
    | ~ spl11_0 ),
    inference(unit_resulting_resolution,[],[f109,f110,f111,f112,f113,f114,f115,f116,f180,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v14_waybel_0(X1,X0)
      | r2_hidden(sK6(X0,X1),X1)
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f126497,plain,
    ( r1_orders_2(sK0,sK8(k5_waybel_0(sK0,sK6(sK0,sK1)),sK1),sK6(sK0,sK1))
    | ~ spl11_0
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f112,f109,f2919,f124842,f124949,f2070])).

fof(f2070,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK8(k5_waybel_0(X6,X7),X8),u1_struct_0(X6))
      | r1_orders_2(X6,sK8(k5_waybel_0(X6,X7),X8),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | v2_struct_0(X6)
      | r1_tarski(k5_waybel_0(X6,X7),X8) ) ),
    inference(resolution,[],[f136,f150])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f2902,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f2901])).

fof(f2901,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f2883,f2870])).

fof(f2870,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f112,f186,f2777,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f2777,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f109,f110,f111,f112,f113,f114,f115,f177,f2220,f186,f116,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v14_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f2220,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(forward_demodulation,[],[f2219,f193])).

fof(f193,plain,
    ( k5_waybel_0(sK0,sK2) = sK1
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl11_4
  <=> k5_waybel_0(sK0,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f2219,plain,
    ( r2_hidden(sK2,k5_waybel_0(sK0,sK2))
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f109,f112,f186,f186,f2204,f137])).

fof(f2204,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f109,f110,f112,f186,f1365,f186,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t48_waybel_0.p',redefinition_r3_orders_2)).

fof(f1365,plain,
    ( r3_orders_2(sK0,sK2,sK2)
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f109,f110,f112,f186,f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | r3_orders_2(X1,X0,X0)
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t48_waybel_0.p',reflexivity_r3_orders_2)).

fof(f177,plain,
    ( ~ v14_waybel_0(sK1,sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl11_1
  <=> ~ v14_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f186,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl11_2
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f2883,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK2),sK2)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f2872,f2075])).

fof(f2075,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f2074,f1399])).

fof(f2074,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f2073,f109])).

fof(f2073,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f2072,f112])).

fof(f2072,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f2071,f186])).

fof(f2071,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_4 ),
    inference(superposition,[],[f136,f193])).

fof(f2872,plain,
    ( r2_hidden(sK5(sK0,sK1,sK2),sK1)
    | ~ spl11_1
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f112,f186,f2777,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f530,plain,
    ( ~ spl11_1
    | spl11_18 ),
    inference(avatar_split_clause,[],[f119,f528,f176])).

fof(f119,plain,(
    ! [X2] :
      ( k5_waybel_0(sK0,X2) != sK1
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v14_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f194,plain,
    ( spl11_0
    | spl11_4 ),
    inference(avatar_split_clause,[],[f118,f192,f179])).

fof(f118,plain,
    ( k5_waybel_0(sK0,sK2) = sK1
    | v14_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f187,plain,
    ( spl11_0
    | spl11_2 ),
    inference(avatar_split_clause,[],[f117,f185,f179])).

fof(f117,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | v14_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f80])).
%------------------------------------------------------------------------------
