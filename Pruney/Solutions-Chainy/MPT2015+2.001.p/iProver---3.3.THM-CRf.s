%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:42 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 988 expanded)
%              Number of clauses        :  141 ( 321 expanded)
%              Number of leaves         :   24 ( 267 expanded)
%              Depth                    :   26
%              Number of atoms          : 1021 (5582 expanded)
%              Number of equality atoms :  235 ( 431 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ( m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
                & v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ( m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
                  & v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
                | ~ v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
                | ~ v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
            | ~ v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ( ~ m1_yellow_6(k4_waybel_9(X0,X1,sK7),X0,X1)
          | ~ v2_yellow_6(k4_waybel_9(X0,X1,sK7),X0,X1) )
        & m1_subset_1(sK7,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
                | ~ v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ~ m1_yellow_6(k4_waybel_9(X0,sK6,X2),X0,sK6)
              | ~ v2_yellow_6(k4_waybel_9(X0,sK6,X2),X0,sK6) )
            & m1_subset_1(X2,u1_struct_0(sK6)) )
        & l1_waybel_0(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
                  | ~ v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_yellow_6(k4_waybel_9(sK5,X1,X2),sK5,X1)
                | ~ v2_yellow_6(k4_waybel_9(sK5,X1,X2),sK5,X1) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
      | ~ v2_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6) )
    & m1_subset_1(sK7,u1_struct_0(sK6))
    & l1_waybel_0(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_struct_0(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f37,f60,f59,f58])).

fof(f102,plain,(
    m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,(
    l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f99,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,X1) = k1_toler_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k1_toler_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k1_toler_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X2,X0,X1,X3] :
      ( ( k4_waybel_9(X0,X1,X2) = X3
      <=> sP0(X3,X1,X0,X2) )
      | ~ sP1(X2,X0,X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f38,plain,(
    ! [X3,X1,X0,X2] :
      ( sP0(X3,X1,X0,X2)
    <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
        & ! [X4] :
            ( r2_hidden(X4,u1_struct_0(X3))
          <=> ? [X5] :
                ( r1_orders_2(X1,X2,X5)
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X2,X0,X1,X3)
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f31,f39,f38])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X0,X1,X3)
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f49,plain,(
    ! [X2,X0,X1,X3] :
      ( ( ( k4_waybel_9(X0,X1,X2) = X3
          | ~ sP0(X3,X1,X0,X2) )
        & ( sP0(X3,X1,X0,X2)
          | k4_waybel_9(X0,X1,X2) != X3 ) )
      | ~ sP1(X2,X0,X1,X3) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k4_waybel_9(X1,X2,X0) = X3
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | k4_waybel_9(X1,X2,X0) != X3 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f49])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | k4_waybel_9(X1,X2,X0) != X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0)
      | ~ sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f51,plain,(
    ! [X3,X1,X0,X2] :
      ( ( sP0(X3,X1,X0,X2)
        | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
        | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_orders_2(X1,X2,X5)
                  | X4 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | ~ r2_hidden(X4,u1_struct_0(X3)) )
            & ( ? [X5] :
                  ( r1_orders_2(X1,X2,X5)
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X4,u1_struct_0(X3)) ) ) )
      & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
          & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
          & ! [X4] :
              ( ( r2_hidden(X4,u1_struct_0(X3))
                | ! [X5] :
                    ( ~ r1_orders_2(X1,X2,X5)
                    | X4 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( r1_orders_2(X1,X2,X5)
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
        | ~ sP0(X3,X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X3,X1,X0,X2] :
      ( ( sP0(X3,X1,X0,X2)
        | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
        | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_orders_2(X1,X2,X5)
                  | X4 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | ~ r2_hidden(X4,u1_struct_0(X3)) )
            & ( ? [X5] :
                  ( r1_orders_2(X1,X2,X5)
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X4,u1_struct_0(X3)) ) ) )
      & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
          & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
          & ! [X4] :
              ( ( r2_hidden(X4,u1_struct_0(X3))
                | ! [X5] :
                    ( ~ r1_orders_2(X1,X2,X5)
                    | X4 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( r1_orders_2(X1,X2,X5)
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
        | ~ sP0(X3,X1,X0,X2) ) ) ),
    inference(flattening,[],[f51])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
        | ~ r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_orders_2(X1,X3,X5)
                  | X4 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | ~ r2_hidden(X4,u1_struct_0(X0)) )
            & ( ? [X6] :
                  ( r1_orders_2(X1,X3,X6)
                  & X4 = X6
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              | r2_hidden(X4,u1_struct_0(X0)) ) ) )
      & ( ( u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
          & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
          & ! [X7] :
              ( ( r2_hidden(X7,u1_struct_0(X0))
                | ! [X8] :
                    ( ~ r1_orders_2(X1,X3,X8)
                    | X7 != X8
                    | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
              & ( ? [X9] :
                    ( r1_orders_2(X1,X3,X9)
                    & X7 = X9
                    & m1_subset_1(X9,u1_struct_0(X1)) )
                | ~ r2_hidden(X7,u1_struct_0(X0)) ) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f52])).

fof(f56,plain,(
    ! [X7,X3,X1] :
      ( ? [X9] :
          ( r1_orders_2(X1,X3,X9)
          & X7 = X9
          & m1_subset_1(X9,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X3,sK4(X1,X3,X7))
        & sK4(X1,X3,X7) = X7
        & m1_subset_1(sK4(X1,X3,X7),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X4,X3,X1,X0] :
      ( ? [X6] :
          ( r1_orders_2(X1,X3,X6)
          & X4 = X6
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X3,sK3(X0,X1,X3))
        & sK3(X0,X1,X3) = X4
        & m1_subset_1(sK3(X0,X1,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_orders_2(X1,X3,X5)
                | X4 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(X4,u1_struct_0(X0)) )
          & ( ? [X6] :
                ( r1_orders_2(X1,X3,X6)
                & X4 = X6
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | r2_hidden(X4,u1_struct_0(X0)) ) )
     => ( ( ! [X5] :
              ( ~ r1_orders_2(X1,X3,X5)
              | sK2(X0,X1,X3) != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(sK2(X0,X1,X3),u1_struct_0(X0)) )
        & ( ? [X6] :
              ( r1_orders_2(X1,X3,X6)
              & sK2(X0,X1,X3) = X6
              & m1_subset_1(X6,u1_struct_0(X1)) )
          | r2_hidden(sK2(X0,X1,X3),u1_struct_0(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
        | ~ r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
        | ( ( ! [X5] :
                ( ~ r1_orders_2(X1,X3,X5)
                | sK2(X0,X1,X3) != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(sK2(X0,X1,X3),u1_struct_0(X0)) )
          & ( ( r1_orders_2(X1,X3,sK3(X0,X1,X3))
              & sK2(X0,X1,X3) = sK3(X0,X1,X3)
              & m1_subset_1(sK3(X0,X1,X3),u1_struct_0(X1)) )
            | r2_hidden(sK2(X0,X1,X3),u1_struct_0(X0)) ) ) )
      & ( ( u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
          & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
          & ! [X7] :
              ( ( r2_hidden(X7,u1_struct_0(X0))
                | ! [X8] :
                    ( ~ r1_orders_2(X1,X3,X8)
                    | X7 != X8
                    | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
              & ( ( r1_orders_2(X1,X3,sK4(X1,X3,X7))
                  & sK4(X1,X3,X7) = X7
                  & m1_subset_1(sK4(X1,X3,X7),u1_struct_0(X1)) )
                | ~ r2_hidden(X7,u1_struct_0(X0)) ) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f53,f56,f55,f54])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f100,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_yellow_0(X1,X0)
      | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_6(X2,X0,X1)
      | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
      | ~ m1_yellow_0(X2,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_yellow_0(X1,X0)
              | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
            & ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
              | ~ v4_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v4_yellow_0(X1,X0)
      | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_yellow_6(X2,X0,X1)
                  | ~ m1_yellow_0(X2,X1)
                  | ~ v4_yellow_0(X2,X1) )
                & ( ( m1_yellow_0(X2,X1)
                    & v4_yellow_0(X2,X1) )
                  | ~ v2_yellow_6(X2,X0,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_yellow_6(X2,X0,X1)
                  | ~ m1_yellow_0(X2,X1)
                  | ~ v4_yellow_0(X2,X1) )
                & ( ( m1_yellow_0(X2,X1)
                    & v4_yellow_0(X2,X1) )
                  | ~ v2_yellow_6(X2,X0,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v2_yellow_6(X2,X0,X1)
      | ~ m1_yellow_0(X2,X1)
      | ~ v4_yellow_0(X2,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,
    ( ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
    | ~ v2_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_4471,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_5128,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4471])).

cnf(c_38,negated_conjecture,
    ( l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_4470,negated_conjecture,
    ( l1_waybel_0(sK6,sK5) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_5129,plain,
    ( l1_waybel_0(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4470])).

cnf(c_13,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_40,negated_conjecture,
    ( l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_813,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_40])).

cnf(c_814,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_5,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_956,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ),
    inference(resolution,[status(thm)],[c_814,c_5])).

cnf(c_4464,plain,
    ( ~ l1_waybel_0(X0_61,sK5)
    | m1_subset_1(u1_orders_2(X0_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X0_61)))) ),
    inference(subtyping,[status(esa)],[c_956])).

cnf(c_5135,plain,
    ( l1_waybel_0(X0_61,sK5) != iProver_top
    | m1_subset_1(u1_orders_2(X0_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X0_61)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4464])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4488,plain,
    ( ~ m1_subset_1(X0_62,k1_zfmisc_1(k2_zfmisc_1(X1_62,X2_62)))
    | v1_relat_1(X0_62) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_5111,plain,
    ( m1_subset_1(X0_62,k1_zfmisc_1(k2_zfmisc_1(X1_62,X2_62))) != iProver_top
    | v1_relat_1(X0_62) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4488])).

cnf(c_5440,plain,
    ( l1_waybel_0(X0_61,sK5) != iProver_top
    | v1_relat_1(u1_orders_2(X0_61)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5135,c_5111])).

cnf(c_5698,plain,
    ( v1_relat_1(u1_orders_2(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5129,c_5440])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_toler_1(X0,X1) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4484,plain,
    ( ~ v1_relat_1(X0_62)
    | k1_toler_1(X0_62,X1_62) = k2_wellord1(X0_62,X1_62) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_5115,plain,
    ( k1_toler_1(X0_62,X1_62) = k2_wellord1(X0_62,X1_62)
    | v1_relat_1(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4484])).

cnf(c_5717,plain,
    ( k1_toler_1(u1_orders_2(sK6),X0_62) = k2_wellord1(u1_orders_2(sK6),X0_62) ),
    inference(superposition,[status(thm)],[c_5698,c_5115])).

cnf(c_32,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ v6_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_34,plain,
    ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_522,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(X4,X5)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X5)
    | X5 != X1
    | k4_waybel_9(X5,X4,X6) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_34])).

cnf(c_523,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(k4_waybel_9(X1,X3,X4),X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_33,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_547,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_523,c_33])).

cnf(c_738,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_547,c_40])).

cnf(c_739,plain,
    ( sP1(X0,sK5,X1,k4_waybel_9(sK5,X2,X3))
    | ~ l1_waybel_0(X2,sK5)
    | ~ l1_waybel_0(X1,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_738])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_743,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,sK5)
    | ~ l1_waybel_0(X2,sK5)
    | sP1(X0,sK5,X1,k4_waybel_9(sK5,X2,X3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_739,c_41])).

cnf(c_744,plain,
    ( sP1(X0,sK5,X1,k4_waybel_9(sK5,X2,X3))
    | ~ l1_waybel_0(X2,sK5)
    | ~ l1_waybel_0(X1,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_743])).

cnf(c_4467,plain,
    ( sP1(X0_62,sK5,X0_61,k4_waybel_9(sK5,X1_61,X1_62))
    | ~ l1_waybel_0(X0_61,sK5)
    | ~ l1_waybel_0(X1_61,sK5)
    | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | ~ m1_subset_1(X1_62,u1_struct_0(X1_61))
    | v2_struct_0(X0_61)
    | v2_struct_0(X1_61) ),
    inference(subtyping,[status(esa)],[c_744])).

cnf(c_5132,plain,
    ( sP1(X0_62,sK5,X0_61,k4_waybel_9(sK5,X1_61,X1_62)) = iProver_top
    | l1_waybel_0(X1_61,sK5) != iProver_top
    | l1_waybel_0(X0_61,sK5) != iProver_top
    | m1_subset_1(X1_62,u1_struct_0(X1_61)) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | v2_struct_0(X1_61) = iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4467])).

cnf(c_21,plain,
    ( ~ sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0))
    | sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_4482,plain,
    ( ~ sP1(X0_62,X0_61,X1_61,k4_waybel_9(X0_61,X1_61,X0_62))
    | sP0(k4_waybel_9(X0_61,X1_61,X0_62),X1_61,X0_61,X0_62) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_5117,plain,
    ( sP1(X0_62,X0_61,X1_61,k4_waybel_9(X0_61,X1_61,X0_62)) != iProver_top
    | sP0(k4_waybel_9(X0_61,X1_61,X0_62),X1_61,X0_61,X0_62) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4482])).

cnf(c_6040,plain,
    ( sP0(k4_waybel_9(sK5,X0_61,X0_62),X0_61,sK5,X0_62) = iProver_top
    | l1_waybel_0(X0_61,sK5) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_5132,c_5117])).

cnf(c_27,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4476,plain,
    ( ~ sP0(X0_61,X1_61,X2_61,X0_62)
    | r2_relset_1(u1_struct_0(X0_61),u1_struct_0(X0_61),u1_orders_2(X0_61),k1_toler_1(u1_orders_2(X1_61),u1_struct_0(X0_61))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_5123,plain,
    ( sP0(X0_61,X1_61,X2_61,X0_62) != iProver_top
    | r2_relset_1(u1_struct_0(X0_61),u1_struct_0(X0_61),u1_orders_2(X0_61),k1_toler_1(u1_orders_2(X1_61),u1_struct_0(X0_61))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4476])).

cnf(c_6187,plain,
    ( r2_relset_1(u1_struct_0(k4_waybel_9(sK5,X0_61,X0_62)),u1_struct_0(k4_waybel_9(sK5,X0_61,X0_62)),u1_orders_2(k4_waybel_9(sK5,X0_61,X0_62)),k1_toler_1(u1_orders_2(X0_61),u1_struct_0(k4_waybel_9(sK5,X0_61,X0_62)))) = iProver_top
    | l1_waybel_0(X0_61,sK5) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
    | v2_struct_0(X0_61) = iProver_top ),
    inference(superposition,[status(thm)],[c_6040,c_5123])).

cnf(c_7836,plain,
    ( r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))) = iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5717,c_6187])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_44,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_45,plain,
    ( l1_waybel_0(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_8210,plain,
    ( m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
    | r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7836,c_44,c_45])).

cnf(c_8211,plain,
    ( r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))) = iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8210])).

cnf(c_4,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4486,plain,
    ( ~ r2_relset_1(X0_62,X1_62,X2_62,X3_62)
    | ~ m1_subset_1(X2_62,k1_zfmisc_1(k2_zfmisc_1(X0_62,X1_62)))
    | ~ m1_subset_1(X3_62,k1_zfmisc_1(k2_zfmisc_1(X0_62,X1_62)))
    | X3_62 = X2_62 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_5113,plain,
    ( X0_62 = X1_62
    | r2_relset_1(X2_62,X3_62,X1_62,X0_62) != iProver_top
    | m1_subset_1(X1_62,k1_zfmisc_1(k2_zfmisc_1(X2_62,X3_62))) != iProver_top
    | m1_subset_1(X0_62,k1_zfmisc_1(k2_zfmisc_1(X2_62,X3_62))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4486])).

cnf(c_6646,plain,
    ( u1_orders_2(X0_61) = X0_62
    | r2_relset_1(u1_struct_0(X0_61),u1_struct_0(X0_61),u1_orders_2(X0_61),X0_62) != iProver_top
    | l1_waybel_0(X0_61,sK5) != iProver_top
    | m1_subset_1(X0_62,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X0_61)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5135,c_5113])).

cnf(c_8218,plain,
    ( k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))) = u1_orders_2(k4_waybel_9(sK5,sK6,X0_62))
    | l1_waybel_0(k4_waybel_9(sK5,sK6,X0_62),sK5) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8211,c_6646])).

cnf(c_791,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_40])).

cnf(c_792,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | l1_waybel_0(k4_waybel_9(sK5,X0,X1),sK5)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_791])).

cnf(c_796,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | l1_waybel_0(k4_waybel_9(sK5,X0,X1),sK5)
    | ~ l1_waybel_0(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_792,c_41])).

cnf(c_797,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | l1_waybel_0(k4_waybel_9(sK5,X0,X1),sK5)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_796])).

cnf(c_4465,plain,
    ( ~ l1_waybel_0(X0_61,sK5)
    | l1_waybel_0(k4_waybel_9(sK5,X0_61,X0_62),sK5)
    | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | v2_struct_0(X0_61) ),
    inference(subtyping,[status(esa)],[c_797])).

cnf(c_5370,plain,
    ( l1_waybel_0(k4_waybel_9(sK5,sK6,X0_62),sK5)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0_62,u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4465])).

cnf(c_5371,plain,
    ( l1_waybel_0(k4_waybel_9(sK5,sK6,X0_62),sK5) = iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5370])).

cnf(c_9298,plain,
    ( k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))) = u1_orders_2(k4_waybel_9(sK5,sK6,X0_62))
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8218,c_44,c_45,c_5371])).

cnf(c_11,plain,
    ( m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4485,plain,
    ( m1_subset_1(k1_toler_1(X0_62,X1_62),k1_zfmisc_1(k2_zfmisc_1(X1_62,X1_62)))
    | ~ v1_relat_1(X0_62) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_5114,plain,
    ( m1_subset_1(k1_toler_1(X0_62,X1_62),k1_zfmisc_1(k2_zfmisc_1(X1_62,X1_62))) = iProver_top
    | v1_relat_1(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4485])).

cnf(c_5782,plain,
    ( m1_subset_1(k2_wellord1(u1_orders_2(sK6),X0_62),k1_zfmisc_1(k2_zfmisc_1(X0_62,X0_62))) = iProver_top
    | v1_relat_1(u1_orders_2(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5717,c_5114])).

cnf(c_5385,plain,
    ( ~ l1_waybel_0(sK6,sK5)
    | m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) ),
    inference(instantiation,[status(thm)],[c_4464])).

cnf(c_5386,plain,
    ( l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5385])).

cnf(c_5455,plain,
    ( ~ m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
    | v1_relat_1(u1_orders_2(sK6)) ),
    inference(instantiation,[status(thm)],[c_4488])).

cnf(c_5456,plain,
    ( m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) != iProver_top
    | v1_relat_1(u1_orders_2(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5455])).

cnf(c_5947,plain,
    ( m1_subset_1(k2_wellord1(u1_orders_2(sK6),X0_62),k1_zfmisc_1(k2_zfmisc_1(X0_62,X0_62))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5782,c_45,c_5386,c_5456])).

cnf(c_9307,plain,
    ( k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))) = u1_orders_2(k4_waybel_9(sK5,sK6,X0_62))
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9298,c_5947])).

cnf(c_9311,plain,
    ( k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) = u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
    inference(superposition,[status(thm)],[c_5128,c_9307])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4489,plain,
    ( ~ v1_relat_1(X0_62)
    | k3_xboole_0(X0_62,k2_zfmisc_1(X1_62,X1_62)) = k2_wellord1(X0_62,X1_62) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_5110,plain,
    ( k3_xboole_0(X0_62,k2_zfmisc_1(X1_62,X1_62)) = k2_wellord1(X0_62,X1_62)
    | v1_relat_1(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4489])).

cnf(c_5716,plain,
    ( k3_xboole_0(u1_orders_2(sK6),k2_zfmisc_1(X0_62,X0_62)) = k2_wellord1(u1_orders_2(sK6),X0_62) ),
    inference(superposition,[status(thm)],[c_5698,c_5110])).

cnf(c_0,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4490,plain,
    ( r1_tarski(k3_xboole_0(X0_62,X0_64),X0_62) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_5109,plain,
    ( r1_tarski(k3_xboole_0(X0_62,X0_64),X0_62) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4490])).

cnf(c_5787,plain,
    ( r1_tarski(k2_wellord1(u1_orders_2(sK6),X0_62),u1_orders_2(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5716,c_5109])).

cnf(c_9341,plain,
    ( r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9311,c_5787])).

cnf(c_5565,plain,
    ( m1_subset_1(k1_toler_1(u1_orders_2(sK6),X0_62),k1_zfmisc_1(k2_zfmisc_1(X0_62,X0_62)))
    | ~ v1_relat_1(u1_orders_2(sK6)) ),
    inference(instantiation,[status(thm)],[c_4485])).

cnf(c_7474,plain,
    ( m1_subset_1(k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))))
    | ~ v1_relat_1(u1_orders_2(sK6)) ),
    inference(instantiation,[status(thm)],[c_5565])).

cnf(c_7476,plain,
    ( m1_subset_1(k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(k4_waybel_9(sK5,sK6,sK7)))))
    | ~ v1_relat_1(u1_orders_2(sK6)) ),
    inference(instantiation,[status(thm)],[c_7474])).

cnf(c_5988,plain,
    ( ~ r2_relset_1(X0_62,X1_62,u1_orders_2(k4_waybel_9(sK5,sK6,X2_62)),X3_62)
    | ~ m1_subset_1(X3_62,k1_zfmisc_1(k2_zfmisc_1(X0_62,X1_62)))
    | ~ m1_subset_1(u1_orders_2(k4_waybel_9(sK5,sK6,X2_62)),k1_zfmisc_1(k2_zfmisc_1(X0_62,X1_62)))
    | X3_62 = u1_orders_2(k4_waybel_9(sK5,sK6,X2_62)) ),
    inference(instantiation,[status(thm)],[c_4486])).

cnf(c_6400,plain,
    ( ~ r2_relset_1(X0_62,X0_62,u1_orders_2(k4_waybel_9(sK5,sK6,X1_62)),k1_toler_1(u1_orders_2(sK6),X0_62))
    | ~ m1_subset_1(k1_toler_1(u1_orders_2(sK6),X0_62),k1_zfmisc_1(k2_zfmisc_1(X0_62,X0_62)))
    | ~ m1_subset_1(u1_orders_2(k4_waybel_9(sK5,sK6,X1_62)),k1_zfmisc_1(k2_zfmisc_1(X0_62,X0_62)))
    | k1_toler_1(u1_orders_2(sK6),X0_62) = u1_orders_2(k4_waybel_9(sK5,sK6,X1_62)) ),
    inference(instantiation,[status(thm)],[c_5988])).

cnf(c_6761,plain,
    ( ~ r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))))
    | ~ m1_subset_1(k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))))
    | ~ m1_subset_1(u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))) = u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)) ),
    inference(instantiation,[status(thm)],[c_6400])).

cnf(c_6763,plain,
    ( ~ r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))))
    | ~ m1_subset_1(k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(k4_waybel_9(sK5,sK6,sK7)))))
    | ~ m1_subset_1(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(k4_waybel_9(sK5,sK6,sK7)))))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) = u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_6761])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) = u1_waybel_0(X2,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4477,plain,
    ( ~ sP0(X0_61,X1_61,X2_61,X0_62)
    | k2_partfun1(u1_struct_0(X1_61),u1_struct_0(X2_61),u1_waybel_0(X2_61,X1_61),u1_struct_0(X0_61)) = u1_waybel_0(X2_61,X0_61) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_5681,plain,
    ( ~ sP0(k4_waybel_9(sK5,sK6,X0_62),sK6,sK5,X0_62)
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))) = u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,X0_62)) ),
    inference(instantiation,[status(thm)],[c_4477])).

cnf(c_5688,plain,
    ( ~ sP0(k4_waybel_9(sK5,sK6,sK7),sK6,sK5,sK7)
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) = u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_5681])).

cnf(c_5682,plain,
    ( ~ sP0(k4_waybel_9(sK5,sK6,X0_62),sK6,sK5,X0_62)
    | r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))) ),
    inference(instantiation,[status(thm)],[c_4476])).

cnf(c_5684,plain,
    ( ~ sP0(k4_waybel_9(sK5,sK6,sK7),sK6,sK5,sK7)
    | r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7)))) ),
    inference(instantiation,[status(thm)],[c_5682])).

cnf(c_6,plain,
    ( m1_yellow_0(X0,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_14,plain,
    ( m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1)
    | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) != u1_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_9,plain,
    ( v4_yellow_0(X0,X1)
    | ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)) != u1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_17,plain,
    ( v2_yellow_6(X0,X1,X2)
    | ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v4_yellow_0(X0,X2)
    | ~ m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,negated_conjecture,
    ( ~ v2_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
    | ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_664,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
    | ~ l1_waybel_0(X2,X1)
    | ~ v4_yellow_0(X0,X2)
    | ~ m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1)
    | k4_waybel_9(sK5,sK6,sK7) != X0
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_36])).

cnf(c_665,plain,
    ( ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ v4_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
    | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
    | ~ l1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_667,plain,
    ( ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
    | ~ v4_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
    | ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_40,c_38])).

cnf(c_668,plain,
    ( ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
    | ~ v4_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
    | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6) ),
    inference(renaming,[status(thm)],[c_667])).

cnf(c_686,plain,
    ( ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
    | ~ m1_yellow_0(X0,X1)
    | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
    | ~ l1_orders_2(X1)
    | k4_waybel_9(sK5,sK6,sK7) != X0
    | k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)) != u1_orders_2(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_668])).

cnf(c_687,plain,
    ( ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
    | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
    | ~ l1_orders_2(sK6)
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_709,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_0(X0,X2)
    | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
    | ~ l1_struct_0(X1)
    | ~ l1_orders_2(sK6)
    | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) != u1_waybel_0(X1,X0)
    | k4_waybel_9(sK5,sK6,sK7) != X0
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7))
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_687])).

cnf(c_710,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
    | ~ l1_struct_0(sK5)
    | ~ l1_orders_2(sK6)
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_712,plain,
    ( ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
    | ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
    | ~ l1_orders_2(sK6)
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_710,c_40,c_38])).

cnf(c_713,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
    | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
    | ~ l1_orders_2(sK6)
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_712])).

cnf(c_924,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(sK6)
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k4_waybel_9(sK5,sK6,sK7) != X0
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_713])).

cnf(c_925,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6))
    | ~ r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6))
    | ~ l1_orders_2(k4_waybel_9(sK5,sK6,sK7))
    | ~ l1_orders_2(sK6)
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_924])).

cnf(c_941,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6))
    | ~ r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6))
    | ~ l1_orders_2(sK6)
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_925,c_814])).

cnf(c_967,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6))
    | ~ r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6))
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_814,c_941])).

cnf(c_968,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6))
    | ~ r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6))
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_967])).

cnf(c_970,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6))
    | ~ r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6))
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_968,c_38])).

cnf(c_4463,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6))
    | ~ r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6))
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_970])).

cnf(c_5136,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7))
    | l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6)) != iProver_top
    | r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4463])).

cnf(c_46,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4609,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7))
    | l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6)) != iProver_top
    | r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4463])).

cnf(c_5373,plain,
    ( l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5) = iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5371])).

cnf(c_35,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_tarski(u1_struct_0(k4_waybel_9(X1,X0,X2)),u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_769,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_tarski(u1_struct_0(k4_waybel_9(X1,X0,X2)),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_40])).

cnf(c_770,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK5,X0,X1)),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_774,plain,
    ( v2_struct_0(X0)
    | r1_tarski(u1_struct_0(k4_waybel_9(sK5,X0,X1)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_770,c_41])).

cnf(c_775,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK5,X0,X1)),u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_774])).

cnf(c_4466,plain,
    ( ~ l1_waybel_0(X0_61,sK5)
    | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK5,X0_61,X0_62)),u1_struct_0(X0_61))
    | v2_struct_0(X0_61) ),
    inference(subtyping,[status(esa)],[c_775])).

cnf(c_5375,plain,
    ( ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0_62,u1_struct_0(sK6))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4466])).

cnf(c_5376,plain,
    ( l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(sK6)) = iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5375])).

cnf(c_5378,plain,
    ( l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6)) = iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5376])).

cnf(c_5591,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
    | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7))
    | r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5136,c_44,c_45,c_46,c_4609,c_5373,c_5378])).

cnf(c_5542,plain,
    ( ~ sP1(X0_62,sK5,sK6,k4_waybel_9(sK5,sK6,X0_62))
    | sP0(k4_waybel_9(sK5,sK6,X0_62),sK6,sK5,X0_62) ),
    inference(instantiation,[status(thm)],[c_4482])).

cnf(c_5544,plain,
    ( ~ sP1(sK7,sK5,sK6,k4_waybel_9(sK5,sK6,sK7))
    | sP0(k4_waybel_9(sK5,sK6,sK7),sK6,sK5,sK7) ),
    inference(instantiation,[status(thm)],[c_5542])).

cnf(c_5380,plain,
    ( sP1(X0_62,sK5,sK6,k4_waybel_9(sK5,X0_61,X1_62))
    | ~ l1_waybel_0(X0_61,sK5)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X1_62,u1_struct_0(X0_61))
    | ~ m1_subset_1(X0_62,u1_struct_0(sK6))
    | v2_struct_0(X0_61)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4467])).

cnf(c_5517,plain,
    ( sP1(X0_62,sK5,sK6,k4_waybel_9(sK5,sK6,X1_62))
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0_62,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_62,u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_5380])).

cnf(c_5519,plain,
    ( sP1(sK7,sK5,sK6,k4_waybel_9(sK5,sK6,sK7))
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_5517])).

cnf(c_5463,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,X0_62),sK5)
    | m1_subset_1(u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))))) ),
    inference(instantiation,[status(thm)],[c_4464])).

cnf(c_5480,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
    | m1_subset_1(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))))) ),
    inference(instantiation,[status(thm)],[c_5463])).

cnf(c_5372,plain,
    ( l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_5370])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9341,c_7476,c_6763,c_5688,c_5684,c_5591,c_5544,c_5519,c_5480,c_5455,c_5385,c_5372,c_37,c_38,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.41/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.41/0.99  
% 3.41/0.99  ------  iProver source info
% 3.41/0.99  
% 3.41/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.41/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.41/0.99  git: non_committed_changes: false
% 3.41/0.99  git: last_make_outside_of_git: false
% 3.41/0.99  
% 3.41/0.99  ------ 
% 3.41/0.99  
% 3.41/0.99  ------ Input Options
% 3.41/0.99  
% 3.41/0.99  --out_options                           all
% 3.41/0.99  --tptp_safe_out                         true
% 3.41/0.99  --problem_path                          ""
% 3.41/0.99  --include_path                          ""
% 3.41/0.99  --clausifier                            res/vclausify_rel
% 3.41/0.99  --clausifier_options                    --mode clausify
% 3.41/0.99  --stdin                                 false
% 3.41/0.99  --stats_out                             all
% 3.41/0.99  
% 3.41/0.99  ------ General Options
% 3.41/0.99  
% 3.41/0.99  --fof                                   false
% 3.41/0.99  --time_out_real                         305.
% 3.41/0.99  --time_out_virtual                      -1.
% 3.41/0.99  --symbol_type_check                     false
% 3.41/0.99  --clausify_out                          false
% 3.41/0.99  --sig_cnt_out                           false
% 3.41/0.99  --trig_cnt_out                          false
% 3.41/0.99  --trig_cnt_out_tolerance                1.
% 3.41/0.99  --trig_cnt_out_sk_spl                   false
% 3.41/0.99  --abstr_cl_out                          false
% 3.41/0.99  
% 3.41/0.99  ------ Global Options
% 3.41/0.99  
% 3.41/0.99  --schedule                              default
% 3.41/0.99  --add_important_lit                     false
% 3.41/0.99  --prop_solver_per_cl                    1000
% 3.41/0.99  --min_unsat_core                        false
% 3.41/0.99  --soft_assumptions                      false
% 3.41/0.99  --soft_lemma_size                       3
% 3.41/0.99  --prop_impl_unit_size                   0
% 3.41/0.99  --prop_impl_unit                        []
% 3.41/0.99  --share_sel_clauses                     true
% 3.41/0.99  --reset_solvers                         false
% 3.41/0.99  --bc_imp_inh                            [conj_cone]
% 3.41/0.99  --conj_cone_tolerance                   3.
% 3.41/0.99  --extra_neg_conj                        none
% 3.41/0.99  --large_theory_mode                     true
% 3.41/0.99  --prolific_symb_bound                   200
% 3.41/0.99  --lt_threshold                          2000
% 3.41/0.99  --clause_weak_htbl                      true
% 3.41/0.99  --gc_record_bc_elim                     false
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing Options
% 3.41/0.99  
% 3.41/0.99  --preprocessing_flag                    true
% 3.41/0.99  --time_out_prep_mult                    0.1
% 3.41/0.99  --splitting_mode                        input
% 3.41/0.99  --splitting_grd                         true
% 3.41/0.99  --splitting_cvd                         false
% 3.41/0.99  --splitting_cvd_svl                     false
% 3.41/0.99  --splitting_nvd                         32
% 3.41/0.99  --sub_typing                            true
% 3.41/0.99  --prep_gs_sim                           true
% 3.41/0.99  --prep_unflatten                        true
% 3.41/0.99  --prep_res_sim                          true
% 3.41/0.99  --prep_upred                            true
% 3.41/0.99  --prep_sem_filter                       exhaustive
% 3.41/0.99  --prep_sem_filter_out                   false
% 3.41/0.99  --pred_elim                             true
% 3.41/0.99  --res_sim_input                         true
% 3.41/0.99  --eq_ax_congr_red                       true
% 3.41/0.99  --pure_diseq_elim                       true
% 3.41/0.99  --brand_transform                       false
% 3.41/0.99  --non_eq_to_eq                          false
% 3.41/0.99  --prep_def_merge                        true
% 3.41/0.99  --prep_def_merge_prop_impl              false
% 3.41/0.99  --prep_def_merge_mbd                    true
% 3.41/0.99  --prep_def_merge_tr_red                 false
% 3.41/0.99  --prep_def_merge_tr_cl                  false
% 3.41/0.99  --smt_preprocessing                     true
% 3.41/0.99  --smt_ac_axioms                         fast
% 3.41/0.99  --preprocessed_out                      false
% 3.41/0.99  --preprocessed_stats                    false
% 3.41/0.99  
% 3.41/0.99  ------ Abstraction refinement Options
% 3.41/0.99  
% 3.41/0.99  --abstr_ref                             []
% 3.41/0.99  --abstr_ref_prep                        false
% 3.41/0.99  --abstr_ref_until_sat                   false
% 3.41/0.99  --abstr_ref_sig_restrict                funpre
% 3.41/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/0.99  --abstr_ref_under                       []
% 3.41/0.99  
% 3.41/0.99  ------ SAT Options
% 3.41/0.99  
% 3.41/0.99  --sat_mode                              false
% 3.41/0.99  --sat_fm_restart_options                ""
% 3.41/0.99  --sat_gr_def                            false
% 3.41/0.99  --sat_epr_types                         true
% 3.41/0.99  --sat_non_cyclic_types                  false
% 3.41/0.99  --sat_finite_models                     false
% 3.41/0.99  --sat_fm_lemmas                         false
% 3.41/0.99  --sat_fm_prep                           false
% 3.41/0.99  --sat_fm_uc_incr                        true
% 3.41/0.99  --sat_out_model                         small
% 3.41/0.99  --sat_out_clauses                       false
% 3.41/0.99  
% 3.41/0.99  ------ QBF Options
% 3.41/0.99  
% 3.41/0.99  --qbf_mode                              false
% 3.41/0.99  --qbf_elim_univ                         false
% 3.41/0.99  --qbf_dom_inst                          none
% 3.41/0.99  --qbf_dom_pre_inst                      false
% 3.41/0.99  --qbf_sk_in                             false
% 3.41/0.99  --qbf_pred_elim                         true
% 3.41/0.99  --qbf_split                             512
% 3.41/0.99  
% 3.41/0.99  ------ BMC1 Options
% 3.41/0.99  
% 3.41/0.99  --bmc1_incremental                      false
% 3.41/0.99  --bmc1_axioms                           reachable_all
% 3.41/0.99  --bmc1_min_bound                        0
% 3.41/0.99  --bmc1_max_bound                        -1
% 3.41/0.99  --bmc1_max_bound_default                -1
% 3.41/0.99  --bmc1_symbol_reachability              true
% 3.41/0.99  --bmc1_property_lemmas                  false
% 3.41/0.99  --bmc1_k_induction                      false
% 3.41/0.99  --bmc1_non_equiv_states                 false
% 3.41/0.99  --bmc1_deadlock                         false
% 3.41/0.99  --bmc1_ucm                              false
% 3.41/0.99  --bmc1_add_unsat_core                   none
% 3.41/0.99  --bmc1_unsat_core_children              false
% 3.41/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/0.99  --bmc1_out_stat                         full
% 3.41/0.99  --bmc1_ground_init                      false
% 3.41/0.99  --bmc1_pre_inst_next_state              false
% 3.41/0.99  --bmc1_pre_inst_state                   false
% 3.41/0.99  --bmc1_pre_inst_reach_state             false
% 3.41/0.99  --bmc1_out_unsat_core                   false
% 3.41/0.99  --bmc1_aig_witness_out                  false
% 3.41/0.99  --bmc1_verbose                          false
% 3.41/0.99  --bmc1_dump_clauses_tptp                false
% 3.41/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.41/0.99  --bmc1_dump_file                        -
% 3.41/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.41/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.41/0.99  --bmc1_ucm_extend_mode                  1
% 3.41/0.99  --bmc1_ucm_init_mode                    2
% 3.41/0.99  --bmc1_ucm_cone_mode                    none
% 3.41/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.41/0.99  --bmc1_ucm_relax_model                  4
% 3.41/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.41/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/0.99  --bmc1_ucm_layered_model                none
% 3.41/0.99  --bmc1_ucm_max_lemma_size               10
% 3.41/0.99  
% 3.41/0.99  ------ AIG Options
% 3.41/0.99  
% 3.41/0.99  --aig_mode                              false
% 3.41/0.99  
% 3.41/0.99  ------ Instantiation Options
% 3.41/0.99  
% 3.41/0.99  --instantiation_flag                    true
% 3.41/0.99  --inst_sos_flag                         false
% 3.41/0.99  --inst_sos_phase                        true
% 3.41/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel_side                     num_symb
% 3.41/0.99  --inst_solver_per_active                1400
% 3.41/0.99  --inst_solver_calls_frac                1.
% 3.41/0.99  --inst_passive_queue_type               priority_queues
% 3.41/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/0.99  --inst_passive_queues_freq              [25;2]
% 3.41/0.99  --inst_dismatching                      true
% 3.41/0.99  --inst_eager_unprocessed_to_passive     true
% 3.41/0.99  --inst_prop_sim_given                   true
% 3.41/0.99  --inst_prop_sim_new                     false
% 3.41/0.99  --inst_subs_new                         false
% 3.41/0.99  --inst_eq_res_simp                      false
% 3.41/0.99  --inst_subs_given                       false
% 3.41/0.99  --inst_orphan_elimination               true
% 3.41/0.99  --inst_learning_loop_flag               true
% 3.41/0.99  --inst_learning_start                   3000
% 3.41/0.99  --inst_learning_factor                  2
% 3.41/0.99  --inst_start_prop_sim_after_learn       3
% 3.41/0.99  --inst_sel_renew                        solver
% 3.41/0.99  --inst_lit_activity_flag                true
% 3.41/0.99  --inst_restr_to_given                   false
% 3.41/0.99  --inst_activity_threshold               500
% 3.41/0.99  --inst_out_proof                        true
% 3.41/0.99  
% 3.41/0.99  ------ Resolution Options
% 3.41/0.99  
% 3.41/0.99  --resolution_flag                       true
% 3.41/0.99  --res_lit_sel                           adaptive
% 3.41/0.99  --res_lit_sel_side                      none
% 3.41/0.99  --res_ordering                          kbo
% 3.41/0.99  --res_to_prop_solver                    active
% 3.41/0.99  --res_prop_simpl_new                    false
% 3.41/0.99  --res_prop_simpl_given                  true
% 3.41/0.99  --res_passive_queue_type                priority_queues
% 3.41/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/0.99  --res_passive_queues_freq               [15;5]
% 3.41/0.99  --res_forward_subs                      full
% 3.41/0.99  --res_backward_subs                     full
% 3.41/0.99  --res_forward_subs_resolution           true
% 3.41/0.99  --res_backward_subs_resolution          true
% 3.41/0.99  --res_orphan_elimination                true
% 3.41/0.99  --res_time_limit                        2.
% 3.41/0.99  --res_out_proof                         true
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Options
% 3.41/0.99  
% 3.41/0.99  --superposition_flag                    true
% 3.41/0.99  --sup_passive_queue_type                priority_queues
% 3.41/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.41/0.99  --demod_completeness_check              fast
% 3.41/0.99  --demod_use_ground                      true
% 3.41/0.99  --sup_to_prop_solver                    passive
% 3.41/0.99  --sup_prop_simpl_new                    true
% 3.41/0.99  --sup_prop_simpl_given                  true
% 3.41/0.99  --sup_fun_splitting                     false
% 3.41/0.99  --sup_smt_interval                      50000
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Simplification Setup
% 3.41/0.99  
% 3.41/0.99  --sup_indices_passive                   []
% 3.41/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_full_bw                           [BwDemod]
% 3.41/0.99  --sup_immed_triv                        [TrivRules]
% 3.41/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_immed_bw_main                     []
% 3.41/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  
% 3.41/0.99  ------ Combination Options
% 3.41/0.99  
% 3.41/0.99  --comb_res_mult                         3
% 3.41/0.99  --comb_sup_mult                         2
% 3.41/0.99  --comb_inst_mult                        10
% 3.41/0.99  
% 3.41/0.99  ------ Debug Options
% 3.41/0.99  
% 3.41/0.99  --dbg_backtrace                         false
% 3.41/0.99  --dbg_dump_prop_clauses                 false
% 3.41/0.99  --dbg_dump_prop_clauses_file            -
% 3.41/0.99  --dbg_out_stat                          false
% 3.41/0.99  ------ Parsing...
% 3.41/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/0.99  ------ Proving...
% 3.41/0.99  ------ Problem Properties 
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  clauses                                 28
% 3.41/0.99  conjectures                             4
% 3.41/0.99  EPR                                     3
% 3.41/0.99  Horn                                    22
% 3.41/0.99  unary                                   5
% 3.41/0.99  binary                                  9
% 3.41/0.99  lits                                    84
% 3.41/0.99  lits eq                                 13
% 3.41/0.99  fd_pure                                 0
% 3.41/0.99  fd_pseudo                               0
% 3.41/0.99  fd_cond                                 0
% 3.41/0.99  fd_pseudo_cond                          2
% 3.41/0.99  AC symbols                              0
% 3.41/0.99  
% 3.41/0.99  ------ Schedule dynamic 5 is on 
% 3.41/0.99  
% 3.41/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  ------ 
% 3.41/0.99  Current options:
% 3.41/0.99  ------ 
% 3.41/0.99  
% 3.41/0.99  ------ Input Options
% 3.41/0.99  
% 3.41/0.99  --out_options                           all
% 3.41/0.99  --tptp_safe_out                         true
% 3.41/0.99  --problem_path                          ""
% 3.41/0.99  --include_path                          ""
% 3.41/0.99  --clausifier                            res/vclausify_rel
% 3.41/0.99  --clausifier_options                    --mode clausify
% 3.41/0.99  --stdin                                 false
% 3.41/0.99  --stats_out                             all
% 3.41/0.99  
% 3.41/0.99  ------ General Options
% 3.41/0.99  
% 3.41/0.99  --fof                                   false
% 3.41/0.99  --time_out_real                         305.
% 3.41/0.99  --time_out_virtual                      -1.
% 3.41/0.99  --symbol_type_check                     false
% 3.41/0.99  --clausify_out                          false
% 3.41/0.99  --sig_cnt_out                           false
% 3.41/0.99  --trig_cnt_out                          false
% 3.41/0.99  --trig_cnt_out_tolerance                1.
% 3.41/0.99  --trig_cnt_out_sk_spl                   false
% 3.41/0.99  --abstr_cl_out                          false
% 3.41/0.99  
% 3.41/0.99  ------ Global Options
% 3.41/0.99  
% 3.41/0.99  --schedule                              default
% 3.41/0.99  --add_important_lit                     false
% 3.41/0.99  --prop_solver_per_cl                    1000
% 3.41/0.99  --min_unsat_core                        false
% 3.41/0.99  --soft_assumptions                      false
% 3.41/0.99  --soft_lemma_size                       3
% 3.41/0.99  --prop_impl_unit_size                   0
% 3.41/0.99  --prop_impl_unit                        []
% 3.41/0.99  --share_sel_clauses                     true
% 3.41/0.99  --reset_solvers                         false
% 3.41/0.99  --bc_imp_inh                            [conj_cone]
% 3.41/0.99  --conj_cone_tolerance                   3.
% 3.41/0.99  --extra_neg_conj                        none
% 3.41/0.99  --large_theory_mode                     true
% 3.41/0.99  --prolific_symb_bound                   200
% 3.41/0.99  --lt_threshold                          2000
% 3.41/0.99  --clause_weak_htbl                      true
% 3.41/0.99  --gc_record_bc_elim                     false
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing Options
% 3.41/0.99  
% 3.41/0.99  --preprocessing_flag                    true
% 3.41/0.99  --time_out_prep_mult                    0.1
% 3.41/0.99  --splitting_mode                        input
% 3.41/0.99  --splitting_grd                         true
% 3.41/0.99  --splitting_cvd                         false
% 3.41/0.99  --splitting_cvd_svl                     false
% 3.41/0.99  --splitting_nvd                         32
% 3.41/0.99  --sub_typing                            true
% 3.41/0.99  --prep_gs_sim                           true
% 3.41/0.99  --prep_unflatten                        true
% 3.41/0.99  --prep_res_sim                          true
% 3.41/0.99  --prep_upred                            true
% 3.41/0.99  --prep_sem_filter                       exhaustive
% 3.41/0.99  --prep_sem_filter_out                   false
% 3.41/0.99  --pred_elim                             true
% 3.41/0.99  --res_sim_input                         true
% 3.41/0.99  --eq_ax_congr_red                       true
% 3.41/0.99  --pure_diseq_elim                       true
% 3.41/0.99  --brand_transform                       false
% 3.41/0.99  --non_eq_to_eq                          false
% 3.41/0.99  --prep_def_merge                        true
% 3.41/0.99  --prep_def_merge_prop_impl              false
% 3.41/0.99  --prep_def_merge_mbd                    true
% 3.41/0.99  --prep_def_merge_tr_red                 false
% 3.41/0.99  --prep_def_merge_tr_cl                  false
% 3.41/0.99  --smt_preprocessing                     true
% 3.41/0.99  --smt_ac_axioms                         fast
% 3.41/0.99  --preprocessed_out                      false
% 3.41/0.99  --preprocessed_stats                    false
% 3.41/0.99  
% 3.41/0.99  ------ Abstraction refinement Options
% 3.41/0.99  
% 3.41/0.99  --abstr_ref                             []
% 3.41/0.99  --abstr_ref_prep                        false
% 3.41/0.99  --abstr_ref_until_sat                   false
% 3.41/0.99  --abstr_ref_sig_restrict                funpre
% 3.41/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/0.99  --abstr_ref_under                       []
% 3.41/0.99  
% 3.41/0.99  ------ SAT Options
% 3.41/0.99  
% 3.41/0.99  --sat_mode                              false
% 3.41/0.99  --sat_fm_restart_options                ""
% 3.41/0.99  --sat_gr_def                            false
% 3.41/0.99  --sat_epr_types                         true
% 3.41/0.99  --sat_non_cyclic_types                  false
% 3.41/0.99  --sat_finite_models                     false
% 3.41/0.99  --sat_fm_lemmas                         false
% 3.41/0.99  --sat_fm_prep                           false
% 3.41/0.99  --sat_fm_uc_incr                        true
% 3.41/0.99  --sat_out_model                         small
% 3.41/0.99  --sat_out_clauses                       false
% 3.41/0.99  
% 3.41/0.99  ------ QBF Options
% 3.41/0.99  
% 3.41/0.99  --qbf_mode                              false
% 3.41/0.99  --qbf_elim_univ                         false
% 3.41/0.99  --qbf_dom_inst                          none
% 3.41/0.99  --qbf_dom_pre_inst                      false
% 3.41/0.99  --qbf_sk_in                             false
% 3.41/0.99  --qbf_pred_elim                         true
% 3.41/0.99  --qbf_split                             512
% 3.41/0.99  
% 3.41/0.99  ------ BMC1 Options
% 3.41/0.99  
% 3.41/0.99  --bmc1_incremental                      false
% 3.41/0.99  --bmc1_axioms                           reachable_all
% 3.41/0.99  --bmc1_min_bound                        0
% 3.41/0.99  --bmc1_max_bound                        -1
% 3.41/0.99  --bmc1_max_bound_default                -1
% 3.41/0.99  --bmc1_symbol_reachability              true
% 3.41/0.99  --bmc1_property_lemmas                  false
% 3.41/0.99  --bmc1_k_induction                      false
% 3.41/0.99  --bmc1_non_equiv_states                 false
% 3.41/0.99  --bmc1_deadlock                         false
% 3.41/0.99  --bmc1_ucm                              false
% 3.41/0.99  --bmc1_add_unsat_core                   none
% 3.41/0.99  --bmc1_unsat_core_children              false
% 3.41/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/0.99  --bmc1_out_stat                         full
% 3.41/0.99  --bmc1_ground_init                      false
% 3.41/0.99  --bmc1_pre_inst_next_state              false
% 3.41/0.99  --bmc1_pre_inst_state                   false
% 3.41/0.99  --bmc1_pre_inst_reach_state             false
% 3.41/0.99  --bmc1_out_unsat_core                   false
% 3.41/0.99  --bmc1_aig_witness_out                  false
% 3.41/0.99  --bmc1_verbose                          false
% 3.41/0.99  --bmc1_dump_clauses_tptp                false
% 3.41/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.41/0.99  --bmc1_dump_file                        -
% 3.41/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.41/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.41/0.99  --bmc1_ucm_extend_mode                  1
% 3.41/0.99  --bmc1_ucm_init_mode                    2
% 3.41/0.99  --bmc1_ucm_cone_mode                    none
% 3.41/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.41/0.99  --bmc1_ucm_relax_model                  4
% 3.41/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.41/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/0.99  --bmc1_ucm_layered_model                none
% 3.41/0.99  --bmc1_ucm_max_lemma_size               10
% 3.41/0.99  
% 3.41/0.99  ------ AIG Options
% 3.41/0.99  
% 3.41/0.99  --aig_mode                              false
% 3.41/0.99  
% 3.41/0.99  ------ Instantiation Options
% 3.41/0.99  
% 3.41/0.99  --instantiation_flag                    true
% 3.41/0.99  --inst_sos_flag                         false
% 3.41/0.99  --inst_sos_phase                        true
% 3.41/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel_side                     none
% 3.41/0.99  --inst_solver_per_active                1400
% 3.41/0.99  --inst_solver_calls_frac                1.
% 3.41/0.99  --inst_passive_queue_type               priority_queues
% 3.41/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/0.99  --inst_passive_queues_freq              [25;2]
% 3.41/0.99  --inst_dismatching                      true
% 3.41/0.99  --inst_eager_unprocessed_to_passive     true
% 3.41/0.99  --inst_prop_sim_given                   true
% 3.41/0.99  --inst_prop_sim_new                     false
% 3.41/0.99  --inst_subs_new                         false
% 3.41/0.99  --inst_eq_res_simp                      false
% 3.41/0.99  --inst_subs_given                       false
% 3.41/0.99  --inst_orphan_elimination               true
% 3.41/0.99  --inst_learning_loop_flag               true
% 3.41/0.99  --inst_learning_start                   3000
% 3.41/0.99  --inst_learning_factor                  2
% 3.41/0.99  --inst_start_prop_sim_after_learn       3
% 3.41/0.99  --inst_sel_renew                        solver
% 3.41/0.99  --inst_lit_activity_flag                true
% 3.41/0.99  --inst_restr_to_given                   false
% 3.41/0.99  --inst_activity_threshold               500
% 3.41/0.99  --inst_out_proof                        true
% 3.41/0.99  
% 3.41/0.99  ------ Resolution Options
% 3.41/0.99  
% 3.41/0.99  --resolution_flag                       false
% 3.41/0.99  --res_lit_sel                           adaptive
% 3.41/0.99  --res_lit_sel_side                      none
% 3.41/0.99  --res_ordering                          kbo
% 3.41/0.99  --res_to_prop_solver                    active
% 3.41/0.99  --res_prop_simpl_new                    false
% 3.41/0.99  --res_prop_simpl_given                  true
% 3.41/0.99  --res_passive_queue_type                priority_queues
% 3.41/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/0.99  --res_passive_queues_freq               [15;5]
% 3.41/0.99  --res_forward_subs                      full
% 3.41/0.99  --res_backward_subs                     full
% 3.41/0.99  --res_forward_subs_resolution           true
% 3.41/0.99  --res_backward_subs_resolution          true
% 3.41/0.99  --res_orphan_elimination                true
% 3.41/0.99  --res_time_limit                        2.
% 3.41/0.99  --res_out_proof                         true
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Options
% 3.41/0.99  
% 3.41/0.99  --superposition_flag                    true
% 3.41/0.99  --sup_passive_queue_type                priority_queues
% 3.41/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.41/0.99  --demod_completeness_check              fast
% 3.41/0.99  --demod_use_ground                      true
% 3.41/0.99  --sup_to_prop_solver                    passive
% 3.41/0.99  --sup_prop_simpl_new                    true
% 3.41/0.99  --sup_prop_simpl_given                  true
% 3.41/0.99  --sup_fun_splitting                     false
% 3.41/0.99  --sup_smt_interval                      50000
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Simplification Setup
% 3.41/0.99  
% 3.41/0.99  --sup_indices_passive                   []
% 3.41/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_full_bw                           [BwDemod]
% 3.41/0.99  --sup_immed_triv                        [TrivRules]
% 3.41/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_immed_bw_main                     []
% 3.41/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  
% 3.41/0.99  ------ Combination Options
% 3.41/0.99  
% 3.41/0.99  --comb_res_mult                         3
% 3.41/0.99  --comb_sup_mult                         2
% 3.41/0.99  --comb_inst_mult                        10
% 3.41/0.99  
% 3.41/0.99  ------ Debug Options
% 3.41/0.99  
% 3.41/0.99  --dbg_backtrace                         false
% 3.41/0.99  --dbg_dump_prop_clauses                 false
% 3.41/0.99  --dbg_dump_prop_clauses_file            -
% 3.41/0.99  --dbg_out_stat                          false
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  ------ Proving...
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  % SZS status Theorem for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  fof(f16,conjecture,(
% 3.41/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) & v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f17,negated_conjecture,(
% 3.41/0.99    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) & v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)))))),
% 3.41/0.99    inference(negated_conjecture,[],[f16])).
% 3.41/0.99  
% 3.41/0.99  fof(f36,plain,(
% 3.41/0.99    ? [X0] : (? [X1] : (? [X2] : ((~m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) | ~v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 3.41/0.99    inference(ennf_transformation,[],[f17])).
% 3.41/0.99  
% 3.41/0.99  fof(f37,plain,(
% 3.41/0.99    ? [X0] : (? [X1] : (? [X2] : ((~m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) | ~v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 3.41/0.99    inference(flattening,[],[f36])).
% 3.41/0.99  
% 3.41/0.99  fof(f60,plain,(
% 3.41/0.99    ( ! [X0,X1] : (? [X2] : ((~m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) | ~v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)) & m1_subset_1(X2,u1_struct_0(X1))) => ((~m1_yellow_6(k4_waybel_9(X0,X1,sK7),X0,X1) | ~v2_yellow_6(k4_waybel_9(X0,X1,sK7),X0,X1)) & m1_subset_1(sK7,u1_struct_0(X1)))) )),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f59,plain,(
% 3.41/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) | ~v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((~m1_yellow_6(k4_waybel_9(X0,sK6,X2),X0,sK6) | ~v2_yellow_6(k4_waybel_9(X0,sK6,X2),X0,sK6)) & m1_subset_1(X2,u1_struct_0(sK6))) & l1_waybel_0(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f58,plain,(
% 3.41/0.99    ? [X0] : (? [X1] : (? [X2] : ((~m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) | ~v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_yellow_6(k4_waybel_9(sK5,X1,X2),sK5,X1) | ~v2_yellow_6(k4_waybel_9(sK5,X1,X2),sK5,X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK5) & ~v2_struct_0(X1)) & l1_struct_0(sK5) & ~v2_struct_0(sK5))),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f61,plain,(
% 3.41/0.99    (((~m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6) | ~v2_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)) & m1_subset_1(sK7,u1_struct_0(sK6))) & l1_waybel_0(sK6,sK5) & ~v2_struct_0(sK6)) & l1_struct_0(sK5) & ~v2_struct_0(sK5)),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f37,f60,f59,f58])).
% 3.41/0.99  
% 3.41/0.99  fof(f102,plain,(
% 3.41/0.99    m1_subset_1(sK7,u1_struct_0(sK6))),
% 3.41/0.99    inference(cnf_transformation,[],[f61])).
% 3.41/0.99  
% 3.41/0.99  fof(f101,plain,(
% 3.41/0.99    l1_waybel_0(sK6,sK5)),
% 3.41/0.99    inference(cnf_transformation,[],[f61])).
% 3.41/0.99  
% 3.41/0.99  fof(f10,axiom,(
% 3.41/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f27,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 3.41/0.99    inference(ennf_transformation,[],[f10])).
% 3.41/0.99  
% 3.41/0.99  fof(f75,plain,(
% 3.41/0.99    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f27])).
% 3.41/0.99  
% 3.41/0.99  fof(f99,plain,(
% 3.41/0.99    l1_struct_0(sK5)),
% 3.41/0.99    inference(cnf_transformation,[],[f61])).
% 3.41/0.99  
% 3.41/0.99  fof(f5,axiom,(
% 3.41/0.99    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f22,plain,(
% 3.41/0.99    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.41/0.99    inference(ennf_transformation,[],[f5])).
% 3.41/0.99  
% 3.41/0.99  fof(f67,plain,(
% 3.41/0.99    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f22])).
% 3.41/0.99  
% 3.41/0.99  fof(f3,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f19,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.41/0.99    inference(ennf_transformation,[],[f3])).
% 3.41/0.99  
% 3.41/0.99  fof(f64,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.41/0.99    inference(cnf_transformation,[],[f19])).
% 3.41/0.99  
% 3.41/0.99  fof(f9,axiom,(
% 3.41/0.99    ! [X0,X1] : (v1_relat_1(X0) => k2_wellord1(X0,X1) = k1_toler_1(X0,X1))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f26,plain,(
% 3.41/0.99    ! [X0,X1] : (k2_wellord1(X0,X1) = k1_toler_1(X0,X1) | ~v1_relat_1(X0))),
% 3.41/0.99    inference(ennf_transformation,[],[f9])).
% 3.41/0.99  
% 3.41/0.99  fof(f74,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k1_toler_1(X0,X1) | ~v1_relat_1(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f26])).
% 3.41/0.99  
% 3.41/0.99  fof(f13,axiom,(
% 3.41/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : ((l1_waybel_0(X3,X0) & v6_waybel_0(X3,X0)) => (k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))))))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f30,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | (~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0))) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.41/0.99    inference(ennf_transformation,[],[f13])).
% 3.41/0.99  
% 3.41/0.99  fof(f31,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.41/0.99    inference(flattening,[],[f30])).
% 3.41/0.99  
% 3.41/0.99  fof(f39,plain,(
% 3.41/0.99    ! [X2,X0,X1,X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> sP0(X3,X1,X0,X2)) | ~sP1(X2,X0,X1,X3))),
% 3.41/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.41/0.99  
% 3.41/0.99  fof(f38,plain,(
% 3.41/0.99    ! [X3,X1,X0,X2] : (sP0(X3,X1,X0,X2) <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))))),
% 3.41/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.41/0.99  
% 3.41/0.99  fof(f40,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP1(X2,X0,X1,X3) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.41/0.99    inference(definition_folding,[],[f31,f39,f38])).
% 3.41/0.99  
% 3.41/0.99  fof(f94,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (sP1(X2,X0,X1,X3) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f40])).
% 3.41/0.99  
% 3.41/0.99  fof(f14,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f32,plain,(
% 3.41/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.41/0.99    inference(ennf_transformation,[],[f14])).
% 3.41/0.99  
% 3.41/0.99  fof(f33,plain,(
% 3.41/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.41/0.99    inference(flattening,[],[f32])).
% 3.41/0.99  
% 3.41/0.99  fof(f95,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f33])).
% 3.41/0.99  
% 3.41/0.99  fof(f96,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f33])).
% 3.41/0.99  
% 3.41/0.99  fof(f98,plain,(
% 3.41/0.99    ~v2_struct_0(sK5)),
% 3.41/0.99    inference(cnf_transformation,[],[f61])).
% 3.41/0.99  
% 3.41/0.99  fof(f49,plain,(
% 3.41/0.99    ! [X2,X0,X1,X3] : (((k4_waybel_9(X0,X1,X2) = X3 | ~sP0(X3,X1,X0,X2)) & (sP0(X3,X1,X0,X2) | k4_waybel_9(X0,X1,X2) != X3)) | ~sP1(X2,X0,X1,X3))),
% 3.41/0.99    inference(nnf_transformation,[],[f39])).
% 3.41/0.99  
% 3.41/0.99  fof(f50,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : (((k4_waybel_9(X1,X2,X0) = X3 | ~sP0(X3,X2,X1,X0)) & (sP0(X3,X2,X1,X0) | k4_waybel_9(X1,X2,X0) != X3)) | ~sP1(X0,X1,X2,X3))),
% 3.41/0.99    inference(rectify,[],[f49])).
% 3.41/0.99  
% 3.41/0.99  fof(f82,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0) | k4_waybel_9(X1,X2,X0) != X3 | ~sP1(X0,X1,X2,X3)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f50])).
% 3.41/0.99  
% 3.41/0.99  fof(f105,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) | ~sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0))) )),
% 3.41/0.99    inference(equality_resolution,[],[f82])).
% 3.41/0.99  
% 3.41/0.99  fof(f51,plain,(
% 3.41/0.99    ! [X3,X1,X0,X2] : ((sP0(X3,X1,X0,X2) | (u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X3)))))) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : ((r2_hidden(X4,u1_struct_0(X3)) | ! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))))) | ~sP0(X3,X1,X0,X2)))),
% 3.41/0.99    inference(nnf_transformation,[],[f38])).
% 3.41/0.99  
% 3.41/0.99  fof(f52,plain,(
% 3.41/0.99    ! [X3,X1,X0,X2] : ((sP0(X3,X1,X0,X2) | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X3))))) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : ((r2_hidden(X4,u1_struct_0(X3)) | ! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))))) | ~sP0(X3,X1,X0,X2)))),
% 3.41/0.99    inference(flattening,[],[f51])).
% 3.41/0.99  
% 3.41/0.99  fof(f53,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) | ~r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X3,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X0))) & (? [X6] : (r1_orders_2(X1,X3,X6) & X4 = X6 & m1_subset_1(X6,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X0))))) & ((u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) & ! [X7] : ((r2_hidden(X7,u1_struct_0(X0)) | ! [X8] : (~r1_orders_2(X1,X3,X8) | X7 != X8 | ~m1_subset_1(X8,u1_struct_0(X1)))) & (? [X9] : (r1_orders_2(X1,X3,X9) & X7 = X9 & m1_subset_1(X9,u1_struct_0(X1))) | ~r2_hidden(X7,u1_struct_0(X0))))) | ~sP0(X0,X1,X2,X3)))),
% 3.41/0.99    inference(rectify,[],[f52])).
% 3.41/0.99  
% 3.41/0.99  fof(f56,plain,(
% 3.41/0.99    ! [X7,X3,X1] : (? [X9] : (r1_orders_2(X1,X3,X9) & X7 = X9 & m1_subset_1(X9,u1_struct_0(X1))) => (r1_orders_2(X1,X3,sK4(X1,X3,X7)) & sK4(X1,X3,X7) = X7 & m1_subset_1(sK4(X1,X3,X7),u1_struct_0(X1))))),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f55,plain,(
% 3.41/0.99    ( ! [X4] : (! [X3,X1,X0] : (? [X6] : (r1_orders_2(X1,X3,X6) & X4 = X6 & m1_subset_1(X6,u1_struct_0(X1))) => (r1_orders_2(X1,X3,sK3(X0,X1,X3)) & sK3(X0,X1,X3) = X4 & m1_subset_1(sK3(X0,X1,X3),u1_struct_0(X1))))) )),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f54,plain,(
% 3.41/0.99    ! [X3,X1,X0] : (? [X4] : ((! [X5] : (~r1_orders_2(X1,X3,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X0))) & (? [X6] : (r1_orders_2(X1,X3,X6) & X4 = X6 & m1_subset_1(X6,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X0)))) => ((! [X5] : (~r1_orders_2(X1,X3,X5) | sK2(X0,X1,X3) != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1,X3),u1_struct_0(X0))) & (? [X6] : (r1_orders_2(X1,X3,X6) & sK2(X0,X1,X3) = X6 & m1_subset_1(X6,u1_struct_0(X1))) | r2_hidden(sK2(X0,X1,X3),u1_struct_0(X0)))))),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f57,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) | ~r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) | ((! [X5] : (~r1_orders_2(X1,X3,X5) | sK2(X0,X1,X3) != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(sK2(X0,X1,X3),u1_struct_0(X0))) & ((r1_orders_2(X1,X3,sK3(X0,X1,X3)) & sK2(X0,X1,X3) = sK3(X0,X1,X3) & m1_subset_1(sK3(X0,X1,X3),u1_struct_0(X1))) | r2_hidden(sK2(X0,X1,X3),u1_struct_0(X0))))) & ((u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) & ! [X7] : ((r2_hidden(X7,u1_struct_0(X0)) | ! [X8] : (~r1_orders_2(X1,X3,X8) | X7 != X8 | ~m1_subset_1(X8,u1_struct_0(X1)))) & ((r1_orders_2(X1,X3,sK4(X1,X3,X7)) & sK4(X1,X3,X7) = X7 & m1_subset_1(sK4(X1,X3,X7),u1_struct_0(X1))) | ~r2_hidden(X7,u1_struct_0(X0))))) | ~sP0(X0,X1,X2,X3)))),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f53,f56,f55,f54])).
% 3.41/0.99  
% 3.41/0.99  fof(f88,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) | ~sP0(X0,X1,X2,X3)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f57])).
% 3.41/0.99  
% 3.41/0.99  fof(f100,plain,(
% 3.41/0.99    ~v2_struct_0(sK6)),
% 3.41/0.99    inference(cnf_transformation,[],[f61])).
% 3.41/0.99  
% 3.41/0.99  fof(f4,axiom,(
% 3.41/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f20,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.41/0.99    inference(ennf_transformation,[],[f4])).
% 3.41/0.99  
% 3.41/0.99  fof(f21,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.41/0.99    inference(flattening,[],[f20])).
% 3.41/0.99  
% 3.41/0.99  fof(f41,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.41/0.99    inference(nnf_transformation,[],[f21])).
% 3.41/0.99  
% 3.41/0.99  fof(f65,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.41/0.99    inference(cnf_transformation,[],[f41])).
% 3.41/0.99  
% 3.41/0.99  fof(f8,axiom,(
% 3.41/0.99    ! [X0,X1] : (v1_relat_1(X0) => m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f25,plain,(
% 3.41/0.99    ! [X0,X1] : (m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v1_relat_1(X0))),
% 3.41/0.99    inference(ennf_transformation,[],[f8])).
% 3.41/0.99  
% 3.41/0.99  fof(f73,plain,(
% 3.41/0.99    ( ! [X0,X1] : (m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v1_relat_1(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f25])).
% 3.41/0.99  
% 3.41/0.99  fof(f2,axiom,(
% 3.41/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f18,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) | ~v1_relat_1(X0))),
% 3.41/0.99    inference(ennf_transformation,[],[f2])).
% 3.41/0.99  
% 3.41/0.99  fof(f63,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f18])).
% 3.41/0.99  
% 3.41/0.99  fof(f1,axiom,(
% 3.41/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f62,plain,(
% 3.41/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f1])).
% 3.41/0.99  
% 3.41/0.99  fof(f89,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f57])).
% 3.41/0.99  
% 3.41/0.99  fof(f6,axiom,(
% 3.41/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f23,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.41/0.99    inference(ennf_transformation,[],[f6])).
% 3.41/0.99  
% 3.41/0.99  fof(f42,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.41/0.99    inference(nnf_transformation,[],[f23])).
% 3.41/0.99  
% 3.41/0.99  fof(f43,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.41/0.99    inference(flattening,[],[f42])).
% 3.41/0.99  
% 3.41/0.99  fof(f70,plain,(
% 3.41/0.99    ( ! [X0,X1] : (m1_yellow_0(X1,X0) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f43])).
% 3.41/0.99  
% 3.41/0.99  fof(f11,axiom,(
% 3.41/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (l1_waybel_0(X2,X0) => (m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f28,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 3.41/0.99    inference(ennf_transformation,[],[f11])).
% 3.41/0.99  
% 3.41/0.99  fof(f45,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | (u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1))) & ((u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 3.41/0.99    inference(nnf_transformation,[],[f28])).
% 3.41/0.99  
% 3.41/0.99  fof(f46,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1)) & ((u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 3.41/0.99    inference(flattening,[],[f45])).
% 3.41/0.99  
% 3.41/0.99  fof(f78,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (m1_yellow_6(X2,X0,X1) | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1) | ~l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f46])).
% 3.41/0.99  
% 3.41/0.99  fof(f7,axiom,(
% 3.41/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => (v4_yellow_0(X1,X0) <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f24,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : ((v4_yellow_0(X1,X0) <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 3.41/0.99    inference(ennf_transformation,[],[f7])).
% 3.41/0.99  
% 3.41/0.99  fof(f44,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (((v4_yellow_0(X1,X0) | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))) & (u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) | ~v4_yellow_0(X1,X0))) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 3.41/0.99    inference(nnf_transformation,[],[f24])).
% 3.41/0.99  
% 3.41/0.99  fof(f72,plain,(
% 3.41/0.99    ( ! [X0,X1] : (v4_yellow_0(X1,X0) | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f44])).
% 3.41/0.99  
% 3.41/0.99  fof(f12,axiom,(
% 3.41/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => (v2_yellow_6(X2,X0,X1) <=> (m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1))))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f29,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_yellow_6(X2,X0,X1) <=> (m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 3.41/0.99    inference(ennf_transformation,[],[f12])).
% 3.41/0.99  
% 3.41/0.99  fof(f47,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_yellow_6(X2,X0,X1) | (~m1_yellow_0(X2,X1) | ~v4_yellow_0(X2,X1))) & ((m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1)) | ~v2_yellow_6(X2,X0,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 3.41/0.99    inference(nnf_transformation,[],[f29])).
% 3.41/0.99  
% 3.41/0.99  fof(f48,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_yellow_6(X2,X0,X1) | ~m1_yellow_0(X2,X1) | ~v4_yellow_0(X2,X1)) & ((m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1)) | ~v2_yellow_6(X2,X0,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 3.41/0.99    inference(flattening,[],[f47])).
% 3.41/0.99  
% 3.41/0.99  fof(f81,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (v2_yellow_6(X2,X0,X1) | ~m1_yellow_0(X2,X1) | ~v4_yellow_0(X2,X1) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f48])).
% 3.41/0.99  
% 3.41/0.99  fof(f103,plain,(
% 3.41/0.99    ~m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6) | ~v2_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)),
% 3.41/0.99    inference(cnf_transformation,[],[f61])).
% 3.41/0.99  
% 3.41/0.99  fof(f15,axiom,(
% 3.41/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f34,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.41/0.99    inference(ennf_transformation,[],[f15])).
% 3.41/0.99  
% 3.41/0.99  fof(f35,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.41/0.99    inference(flattening,[],[f34])).
% 3.41/0.99  
% 3.41/0.99  fof(f97,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f35])).
% 3.41/0.99  
% 3.41/0.99  cnf(c_37,negated_conjecture,
% 3.41/0.99      ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 3.41/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4471,negated_conjecture,
% 3.41/0.99      ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_37]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5128,plain,
% 3.41/0.99      ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4471]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_38,negated_conjecture,
% 3.41/0.99      ( l1_waybel_0(sK6,sK5) ),
% 3.41/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4470,negated_conjecture,
% 3.41/0.99      ( l1_waybel_0(sK6,sK5) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_38]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5129,plain,
% 3.41/0.99      ( l1_waybel_0(sK6,sK5) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4470]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_13,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,X1) | ~ l1_struct_0(X1) | l1_orders_2(X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_40,negated_conjecture,
% 3.41/0.99      ( l1_struct_0(sK5) ),
% 3.41/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_813,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,X1) | l1_orders_2(X0) | sK5 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_40]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_814,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,sK5) | l1_orders_2(X0) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_813]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5,plain,
% 3.41/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.41/0.99      | ~ l1_orders_2(X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_956,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,sK5)
% 3.41/0.99      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ),
% 3.41/0.99      inference(resolution,[status(thm)],[c_814,c_5]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4464,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0_61,sK5)
% 3.41/0.99      | m1_subset_1(u1_orders_2(X0_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X0_61)))) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_956]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5135,plain,
% 3.41/0.99      ( l1_waybel_0(X0_61,sK5) != iProver_top
% 3.41/0.99      | m1_subset_1(u1_orders_2(X0_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X0_61)))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4464]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.41/0.99      | v1_relat_1(X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4488,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0_62,k1_zfmisc_1(k2_zfmisc_1(X1_62,X2_62)))
% 3.41/0.99      | v1_relat_1(X0_62) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5111,plain,
% 3.41/0.99      ( m1_subset_1(X0_62,k1_zfmisc_1(k2_zfmisc_1(X1_62,X2_62))) != iProver_top
% 3.41/0.99      | v1_relat_1(X0_62) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4488]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5440,plain,
% 3.41/0.99      ( l1_waybel_0(X0_61,sK5) != iProver_top
% 3.41/0.99      | v1_relat_1(u1_orders_2(X0_61)) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5135,c_5111]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5698,plain,
% 3.41/0.99      ( v1_relat_1(u1_orders_2(sK6)) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5129,c_5440]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_12,plain,
% 3.41/0.99      ( ~ v1_relat_1(X0) | k1_toler_1(X0,X1) = k2_wellord1(X0,X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4484,plain,
% 3.41/0.99      ( ~ v1_relat_1(X0_62)
% 3.41/0.99      | k1_toler_1(X0_62,X1_62) = k2_wellord1(X0_62,X1_62) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5115,plain,
% 3.41/0.99      ( k1_toler_1(X0_62,X1_62) = k2_wellord1(X0_62,X1_62)
% 3.41/0.99      | v1_relat_1(X0_62) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4484]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5717,plain,
% 3.41/0.99      ( k1_toler_1(u1_orders_2(sK6),X0_62) = k2_wellord1(u1_orders_2(sK6),X0_62) ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5698,c_5115]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_32,plain,
% 3.41/0.99      ( sP1(X0,X1,X2,X3)
% 3.41/0.99      | ~ v6_waybel_0(X3,X1)
% 3.41/0.99      | ~ l1_waybel_0(X2,X1)
% 3.41/0.99      | ~ l1_waybel_0(X3,X1)
% 3.41/0.99      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | v2_struct_0(X2)
% 3.41/0.99      | ~ l1_struct_0(X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_34,plain,
% 3.41/0.99      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
% 3.41/0.99      | ~ l1_waybel_0(X1,X0)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.41/0.99      | v2_struct_0(X0)
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | ~ l1_struct_0(X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_522,plain,
% 3.41/0.99      ( sP1(X0,X1,X2,X3)
% 3.41/0.99      | ~ l1_waybel_0(X2,X1)
% 3.41/0.99      | ~ l1_waybel_0(X3,X1)
% 3.41/0.99      | ~ l1_waybel_0(X4,X5)
% 3.41/0.99      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 3.41/0.99      | ~ m1_subset_1(X6,u1_struct_0(X4))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | v2_struct_0(X2)
% 3.41/0.99      | v2_struct_0(X5)
% 3.41/0.99      | v2_struct_0(X4)
% 3.41/0.99      | ~ l1_struct_0(X1)
% 3.41/0.99      | ~ l1_struct_0(X5)
% 3.41/0.99      | X5 != X1
% 3.41/0.99      | k4_waybel_9(X5,X4,X6) != X3 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_34]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_523,plain,
% 3.41/0.99      ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
% 3.41/0.99      | ~ l1_waybel_0(X2,X1)
% 3.41/0.99      | ~ l1_waybel_0(X3,X1)
% 3.41/0.99      | ~ l1_waybel_0(k4_waybel_9(X1,X3,X4),X1)
% 3.41/0.99      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 3.41/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | v2_struct_0(X2)
% 3.41/0.99      | v2_struct_0(X3)
% 3.41/0.99      | ~ l1_struct_0(X1) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_522]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_33,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,X1)
% 3.41/0.99      | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | v2_struct_0(X0)
% 3.41/0.99      | ~ l1_struct_0(X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_547,plain,
% 3.41/0.99      ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
% 3.41/0.99      | ~ l1_waybel_0(X2,X1)
% 3.41/0.99      | ~ l1_waybel_0(X3,X1)
% 3.41/0.99      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 3.41/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | v2_struct_0(X2)
% 3.41/0.99      | v2_struct_0(X3)
% 3.41/0.99      | ~ l1_struct_0(X1) ),
% 3.41/0.99      inference(forward_subsumption_resolution,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_523,c_33]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_738,plain,
% 3.41/0.99      ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
% 3.41/0.99      | ~ l1_waybel_0(X2,X1)
% 3.41/0.99      | ~ l1_waybel_0(X3,X1)
% 3.41/0.99      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 3.41/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | v2_struct_0(X2)
% 3.41/0.99      | v2_struct_0(X3)
% 3.41/0.99      | sK5 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_547,c_40]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_739,plain,
% 3.41/0.99      ( sP1(X0,sK5,X1,k4_waybel_9(sK5,X2,X3))
% 3.41/0.99      | ~ l1_waybel_0(X2,sK5)
% 3.41/0.99      | ~ l1_waybel_0(X1,sK5)
% 3.41/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | v2_struct_0(X2)
% 3.41/0.99      | v2_struct_0(sK5) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_738]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_41,negated_conjecture,
% 3.41/0.99      ( ~ v2_struct_0(sK5) ),
% 3.41/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_743,plain,
% 3.41/0.99      ( v2_struct_0(X2)
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.41/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.41/0.99      | ~ l1_waybel_0(X1,sK5)
% 3.41/0.99      | ~ l1_waybel_0(X2,sK5)
% 3.41/0.99      | sP1(X0,sK5,X1,k4_waybel_9(sK5,X2,X3)) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_739,c_41]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_744,plain,
% 3.41/0.99      ( sP1(X0,sK5,X1,k4_waybel_9(sK5,X2,X3))
% 3.41/0.99      | ~ l1_waybel_0(X2,sK5)
% 3.41/0.99      | ~ l1_waybel_0(X1,sK5)
% 3.41/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | v2_struct_0(X2) ),
% 3.41/0.99      inference(renaming,[status(thm)],[c_743]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4467,plain,
% 3.41/0.99      ( sP1(X0_62,sK5,X0_61,k4_waybel_9(sK5,X1_61,X1_62))
% 3.41/0.99      | ~ l1_waybel_0(X0_61,sK5)
% 3.41/0.99      | ~ l1_waybel_0(X1_61,sK5)
% 3.41/0.99      | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 3.41/0.99      | ~ m1_subset_1(X1_62,u1_struct_0(X1_61))
% 3.41/0.99      | v2_struct_0(X0_61)
% 3.41/0.99      | v2_struct_0(X1_61) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_744]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5132,plain,
% 3.41/0.99      ( sP1(X0_62,sK5,X0_61,k4_waybel_9(sK5,X1_61,X1_62)) = iProver_top
% 3.41/0.99      | l1_waybel_0(X1_61,sK5) != iProver_top
% 3.41/0.99      | l1_waybel_0(X0_61,sK5) != iProver_top
% 3.41/0.99      | m1_subset_1(X1_62,u1_struct_0(X1_61)) != iProver_top
% 3.41/0.99      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 3.41/0.99      | v2_struct_0(X1_61) = iProver_top
% 3.41/0.99      | v2_struct_0(X0_61) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4467]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_21,plain,
% 3.41/0.99      ( ~ sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0))
% 3.41/0.99      | sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4482,plain,
% 3.41/0.99      ( ~ sP1(X0_62,X0_61,X1_61,k4_waybel_9(X0_61,X1_61,X0_62))
% 3.41/0.99      | sP0(k4_waybel_9(X0_61,X1_61,X0_62),X1_61,X0_61,X0_62) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5117,plain,
% 3.41/0.99      ( sP1(X0_62,X0_61,X1_61,k4_waybel_9(X0_61,X1_61,X0_62)) != iProver_top
% 3.41/0.99      | sP0(k4_waybel_9(X0_61,X1_61,X0_62),X1_61,X0_61,X0_62) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4482]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6040,plain,
% 3.41/0.99      ( sP0(k4_waybel_9(sK5,X0_61,X0_62),X0_61,sK5,X0_62) = iProver_top
% 3.41/0.99      | l1_waybel_0(X0_61,sK5) != iProver_top
% 3.41/0.99      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 3.41/0.99      | v2_struct_0(X0_61) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5132,c_5117]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_27,plain,
% 3.41/0.99      ( ~ sP0(X0,X1,X2,X3)
% 3.41/0.99      | r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) ),
% 3.41/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4476,plain,
% 3.41/0.99      ( ~ sP0(X0_61,X1_61,X2_61,X0_62)
% 3.41/0.99      | r2_relset_1(u1_struct_0(X0_61),u1_struct_0(X0_61),u1_orders_2(X0_61),k1_toler_1(u1_orders_2(X1_61),u1_struct_0(X0_61))) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_27]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5123,plain,
% 3.41/0.99      ( sP0(X0_61,X1_61,X2_61,X0_62) != iProver_top
% 3.41/0.99      | r2_relset_1(u1_struct_0(X0_61),u1_struct_0(X0_61),u1_orders_2(X0_61),k1_toler_1(u1_orders_2(X1_61),u1_struct_0(X0_61))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4476]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6187,plain,
% 3.41/0.99      ( r2_relset_1(u1_struct_0(k4_waybel_9(sK5,X0_61,X0_62)),u1_struct_0(k4_waybel_9(sK5,X0_61,X0_62)),u1_orders_2(k4_waybel_9(sK5,X0_61,X0_62)),k1_toler_1(u1_orders_2(X0_61),u1_struct_0(k4_waybel_9(sK5,X0_61,X0_62)))) = iProver_top
% 3.41/0.99      | l1_waybel_0(X0_61,sK5) != iProver_top
% 3.41/0.99      | m1_subset_1(X0_62,u1_struct_0(X0_61)) != iProver_top
% 3.41/0.99      | v2_struct_0(X0_61) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_6040,c_5123]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_7836,plain,
% 3.41/0.99      ( r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))) = iProver_top
% 3.41/0.99      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.41/0.99      | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
% 3.41/0.99      | v2_struct_0(sK6) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5717,c_6187]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_39,negated_conjecture,
% 3.41/0.99      ( ~ v2_struct_0(sK6) ),
% 3.41/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_44,plain,
% 3.41/0.99      ( v2_struct_0(sK6) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_45,plain,
% 3.41/0.99      ( l1_waybel_0(sK6,sK5) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_8210,plain,
% 3.41/0.99      ( m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
% 3.41/0.99      | r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))) = iProver_top ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_7836,c_44,c_45]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_8211,plain,
% 3.41/0.99      ( r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))) = iProver_top
% 3.41/0.99      | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top ),
% 3.41/0.99      inference(renaming,[status(thm)],[c_8210]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4,plain,
% 3.41/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.41/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.41/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.41/0.99      | X3 = X2 ),
% 3.41/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4486,plain,
% 3.41/0.99      ( ~ r2_relset_1(X0_62,X1_62,X2_62,X3_62)
% 3.41/0.99      | ~ m1_subset_1(X2_62,k1_zfmisc_1(k2_zfmisc_1(X0_62,X1_62)))
% 3.41/0.99      | ~ m1_subset_1(X3_62,k1_zfmisc_1(k2_zfmisc_1(X0_62,X1_62)))
% 3.41/0.99      | X3_62 = X2_62 ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5113,plain,
% 3.41/0.99      ( X0_62 = X1_62
% 3.41/0.99      | r2_relset_1(X2_62,X3_62,X1_62,X0_62) != iProver_top
% 3.41/0.99      | m1_subset_1(X1_62,k1_zfmisc_1(k2_zfmisc_1(X2_62,X3_62))) != iProver_top
% 3.41/0.99      | m1_subset_1(X0_62,k1_zfmisc_1(k2_zfmisc_1(X2_62,X3_62))) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4486]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6646,plain,
% 3.41/0.99      ( u1_orders_2(X0_61) = X0_62
% 3.41/0.99      | r2_relset_1(u1_struct_0(X0_61),u1_struct_0(X0_61),u1_orders_2(X0_61),X0_62) != iProver_top
% 3.41/0.99      | l1_waybel_0(X0_61,sK5) != iProver_top
% 3.41/0.99      | m1_subset_1(X0_62,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_61),u1_struct_0(X0_61)))) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5135,c_5113]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_8218,plain,
% 3.41/0.99      ( k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))) = u1_orders_2(k4_waybel_9(sK5,sK6,X0_62))
% 3.41/0.99      | l1_waybel_0(k4_waybel_9(sK5,sK6,X0_62),sK5) != iProver_top
% 3.41/0.99      | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
% 3.41/0.99      | m1_subset_1(k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))))) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_8211,c_6646]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_791,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,X1)
% 3.41/0.99      | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.41/0.99      | v2_struct_0(X0)
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | sK5 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_40]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_792,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,sK5)
% 3.41/0.99      | l1_waybel_0(k4_waybel_9(sK5,X0,X1),sK5)
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.41/0.99      | v2_struct_0(X0)
% 3.41/0.99      | v2_struct_0(sK5) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_791]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_796,plain,
% 3.41/0.99      ( v2_struct_0(X0)
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.41/0.99      | l1_waybel_0(k4_waybel_9(sK5,X0,X1),sK5)
% 3.41/0.99      | ~ l1_waybel_0(X0,sK5) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_792,c_41]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_797,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,sK5)
% 3.41/0.99      | l1_waybel_0(k4_waybel_9(sK5,X0,X1),sK5)
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.41/0.99      | v2_struct_0(X0) ),
% 3.41/0.99      inference(renaming,[status(thm)],[c_796]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4465,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0_61,sK5)
% 3.41/0.99      | l1_waybel_0(k4_waybel_9(sK5,X0_61,X0_62),sK5)
% 3.41/0.99      | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 3.41/0.99      | v2_struct_0(X0_61) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_797]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5370,plain,
% 3.41/0.99      ( l1_waybel_0(k4_waybel_9(sK5,sK6,X0_62),sK5)
% 3.41/0.99      | ~ l1_waybel_0(sK6,sK5)
% 3.41/0.99      | ~ m1_subset_1(X0_62,u1_struct_0(sK6))
% 3.41/0.99      | v2_struct_0(sK6) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_4465]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5371,plain,
% 3.41/0.99      ( l1_waybel_0(k4_waybel_9(sK5,sK6,X0_62),sK5) = iProver_top
% 3.41/0.99      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.41/0.99      | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
% 3.41/0.99      | v2_struct_0(sK6) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_5370]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9298,plain,
% 3.41/0.99      ( k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))) = u1_orders_2(k4_waybel_9(sK5,sK6,X0_62))
% 3.41/0.99      | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
% 3.41/0.99      | m1_subset_1(k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))))) != iProver_top ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_8218,c_44,c_45,c_5371]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_11,plain,
% 3.41/0.99      ( m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.41/0.99      | ~ v1_relat_1(X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4485,plain,
% 3.41/0.99      ( m1_subset_1(k1_toler_1(X0_62,X1_62),k1_zfmisc_1(k2_zfmisc_1(X1_62,X1_62)))
% 3.41/0.99      | ~ v1_relat_1(X0_62) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5114,plain,
% 3.41/0.99      ( m1_subset_1(k1_toler_1(X0_62,X1_62),k1_zfmisc_1(k2_zfmisc_1(X1_62,X1_62))) = iProver_top
% 3.41/0.99      | v1_relat_1(X0_62) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4485]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5782,plain,
% 3.41/0.99      ( m1_subset_1(k2_wellord1(u1_orders_2(sK6),X0_62),k1_zfmisc_1(k2_zfmisc_1(X0_62,X0_62))) = iProver_top
% 3.41/0.99      | v1_relat_1(u1_orders_2(sK6)) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5717,c_5114]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5385,plain,
% 3.41/0.99      ( ~ l1_waybel_0(sK6,sK5)
% 3.41/0.99      | m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_4464]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5386,plain,
% 3.41/0.99      ( l1_waybel_0(sK6,sK5) != iProver_top
% 3.41/0.99      | m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_5385]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5455,plain,
% 3.41/0.99      ( ~ m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
% 3.41/0.99      | v1_relat_1(u1_orders_2(sK6)) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_4488]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5456,plain,
% 3.41/0.99      ( m1_subset_1(u1_orders_2(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) != iProver_top
% 3.41/0.99      | v1_relat_1(u1_orders_2(sK6)) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_5455]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5947,plain,
% 3.41/0.99      ( m1_subset_1(k2_wellord1(u1_orders_2(sK6),X0_62),k1_zfmisc_1(k2_zfmisc_1(X0_62,X0_62))) = iProver_top ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_5782,c_45,c_5386,c_5456]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9307,plain,
% 3.41/0.99      ( k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))) = u1_orders_2(k4_waybel_9(sK5,sK6,X0_62))
% 3.41/0.99      | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top ),
% 3.41/0.99      inference(forward_subsumption_resolution,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_9298,c_5947]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9311,plain,
% 3.41/0.99      ( k2_wellord1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) = u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5128,c_9307]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1,plain,
% 3.41/0.99      ( ~ v1_relat_1(X0)
% 3.41/0.99      | k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4489,plain,
% 3.41/0.99      ( ~ v1_relat_1(X0_62)
% 3.41/0.99      | k3_xboole_0(X0_62,k2_zfmisc_1(X1_62,X1_62)) = k2_wellord1(X0_62,X1_62) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5110,plain,
% 3.41/0.99      ( k3_xboole_0(X0_62,k2_zfmisc_1(X1_62,X1_62)) = k2_wellord1(X0_62,X1_62)
% 3.41/0.99      | v1_relat_1(X0_62) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4489]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5716,plain,
% 3.41/0.99      ( k3_xboole_0(u1_orders_2(sK6),k2_zfmisc_1(X0_62,X0_62)) = k2_wellord1(u1_orders_2(sK6),X0_62) ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5698,c_5110]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_0,plain,
% 3.41/0.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4490,plain,
% 3.41/0.99      ( r1_tarski(k3_xboole_0(X0_62,X0_64),X0_62) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5109,plain,
% 3.41/0.99      ( r1_tarski(k3_xboole_0(X0_62,X0_64),X0_62) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4490]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5787,plain,
% 3.41/0.99      ( r1_tarski(k2_wellord1(u1_orders_2(sK6),X0_62),u1_orders_2(sK6)) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_5716,c_5109]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9341,plain,
% 3.41/0.99      ( r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6)) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_9311,c_5787]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5565,plain,
% 3.41/0.99      ( m1_subset_1(k1_toler_1(u1_orders_2(sK6),X0_62),k1_zfmisc_1(k2_zfmisc_1(X0_62,X0_62)))
% 3.41/0.99      | ~ v1_relat_1(u1_orders_2(sK6)) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_4485]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_7474,plain,
% 3.41/0.99      ( m1_subset_1(k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))))
% 3.41/0.99      | ~ v1_relat_1(u1_orders_2(sK6)) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_5565]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_7476,plain,
% 3.41/0.99      ( m1_subset_1(k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(k4_waybel_9(sK5,sK6,sK7)))))
% 3.41/0.99      | ~ v1_relat_1(u1_orders_2(sK6)) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_7474]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5988,plain,
% 3.41/0.99      ( ~ r2_relset_1(X0_62,X1_62,u1_orders_2(k4_waybel_9(sK5,sK6,X2_62)),X3_62)
% 3.41/0.99      | ~ m1_subset_1(X3_62,k1_zfmisc_1(k2_zfmisc_1(X0_62,X1_62)))
% 3.41/0.99      | ~ m1_subset_1(u1_orders_2(k4_waybel_9(sK5,sK6,X2_62)),k1_zfmisc_1(k2_zfmisc_1(X0_62,X1_62)))
% 3.41/0.99      | X3_62 = u1_orders_2(k4_waybel_9(sK5,sK6,X2_62)) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_4486]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6400,plain,
% 3.41/0.99      ( ~ r2_relset_1(X0_62,X0_62,u1_orders_2(k4_waybel_9(sK5,sK6,X1_62)),k1_toler_1(u1_orders_2(sK6),X0_62))
% 3.41/0.99      | ~ m1_subset_1(k1_toler_1(u1_orders_2(sK6),X0_62),k1_zfmisc_1(k2_zfmisc_1(X0_62,X0_62)))
% 3.41/0.99      | ~ m1_subset_1(u1_orders_2(k4_waybel_9(sK5,sK6,X1_62)),k1_zfmisc_1(k2_zfmisc_1(X0_62,X0_62)))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),X0_62) = u1_orders_2(k4_waybel_9(sK5,sK6,X1_62)) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_5988]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6761,plain,
% 3.41/0.99      ( ~ r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))))
% 3.41/0.99      | ~ m1_subset_1(k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))))
% 3.41/0.99      | ~ m1_subset_1(u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))) = u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_6400]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6763,plain,
% 3.41/0.99      ( ~ r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))))
% 3.41/0.99      | ~ m1_subset_1(k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(k4_waybel_9(sK5,sK6,sK7)))))
% 3.41/0.99      | ~ m1_subset_1(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(k4_waybel_9(sK5,sK6,sK7)))))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) = u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_6761]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_26,plain,
% 3.41/0.99      ( ~ sP0(X0,X1,X2,X3)
% 3.41/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) = u1_waybel_0(X2,X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4477,plain,
% 3.41/0.99      ( ~ sP0(X0_61,X1_61,X2_61,X0_62)
% 3.41/0.99      | k2_partfun1(u1_struct_0(X1_61),u1_struct_0(X2_61),u1_waybel_0(X2_61,X1_61),u1_struct_0(X0_61)) = u1_waybel_0(X2_61,X0_61) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_26]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5681,plain,
% 3.41/0.99      ( ~ sP0(k4_waybel_9(sK5,sK6,X0_62),sK6,sK5,X0_62)
% 3.41/0.99      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))) = u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,X0_62)) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_4477]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5688,plain,
% 3.41/0.99      ( ~ sP0(k4_waybel_9(sK5,sK6,sK7),sK6,sK5,sK7)
% 3.41/0.99      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) = u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7)) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_5681]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5682,plain,
% 3.41/0.99      ( ~ sP0(k4_waybel_9(sK5,sK6,X0_62),sK6,sK5,X0_62)
% 3.41/0.99      | r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_4476]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5684,plain,
% 3.41/0.99      ( ~ sP0(k4_waybel_9(sK5,sK6,sK7),sK6,sK5,sK7)
% 3.41/0.99      | r2_relset_1(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7)))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_5682]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6,plain,
% 3.41/0.99      ( m1_yellow_0(X0,X1)
% 3.41/0.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.41/0.99      | ~ r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 3.41/0.99      | ~ l1_orders_2(X1)
% 3.41/0.99      | ~ l1_orders_2(X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_14,plain,
% 3.41/0.99      ( m1_yellow_6(X0,X1,X2)
% 3.41/0.99      | ~ l1_waybel_0(X2,X1)
% 3.41/0.99      | ~ l1_waybel_0(X0,X1)
% 3.41/0.99      | ~ m1_yellow_0(X0,X2)
% 3.41/0.99      | ~ l1_struct_0(X1)
% 3.41/0.99      | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) != u1_waybel_0(X1,X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9,plain,
% 3.41/0.99      ( v4_yellow_0(X0,X1)
% 3.41/0.99      | ~ m1_yellow_0(X0,X1)
% 3.41/0.99      | ~ l1_orders_2(X1)
% 3.41/0.99      | k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)) != u1_orders_2(X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_17,plain,
% 3.41/0.99      ( v2_yellow_6(X0,X1,X2)
% 3.41/0.99      | ~ m1_yellow_6(X0,X1,X2)
% 3.41/0.99      | ~ l1_waybel_0(X2,X1)
% 3.41/0.99      | ~ v4_yellow_0(X0,X2)
% 3.41/0.99      | ~ m1_yellow_0(X0,X2)
% 3.41/0.99      | ~ l1_struct_0(X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_36,negated_conjecture,
% 3.41/0.99      ( ~ v2_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
% 3.41/0.99      | ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6) ),
% 3.41/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_664,plain,
% 3.41/0.99      ( ~ m1_yellow_6(X0,X1,X2)
% 3.41/0.99      | ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
% 3.41/0.99      | ~ l1_waybel_0(X2,X1)
% 3.41/0.99      | ~ v4_yellow_0(X0,X2)
% 3.41/0.99      | ~ m1_yellow_0(X0,X2)
% 3.41/0.99      | ~ l1_struct_0(X1)
% 3.41/0.99      | k4_waybel_9(sK5,sK6,sK7) != X0
% 3.41/0.99      | sK6 != X2
% 3.41/0.99      | sK5 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_36]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_665,plain,
% 3.41/0.99      ( ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
% 3.41/0.99      | ~ l1_waybel_0(sK6,sK5)
% 3.41/0.99      | ~ v4_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
% 3.41/0.99      | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
% 3.41/0.99      | ~ l1_struct_0(sK5) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_664]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_667,plain,
% 3.41/0.99      ( ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
% 3.41/0.99      | ~ v4_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
% 3.41/0.99      | ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_665,c_40,c_38]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_668,plain,
% 3.41/0.99      ( ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
% 3.41/0.99      | ~ v4_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
% 3.41/0.99      | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6) ),
% 3.41/0.99      inference(renaming,[status(thm)],[c_667]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_686,plain,
% 3.41/0.99      ( ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
% 3.41/0.99      | ~ m1_yellow_0(X0,X1)
% 3.41/0.99      | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
% 3.41/0.99      | ~ l1_orders_2(X1)
% 3.41/0.99      | k4_waybel_9(sK5,sK6,sK7) != X0
% 3.41/0.99      | k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)) != u1_orders_2(X0)
% 3.41/0.99      | sK6 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_668]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_687,plain,
% 3.41/0.99      ( ~ m1_yellow_6(k4_waybel_9(sK5,sK6,sK7),sK5,sK6)
% 3.41/0.99      | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
% 3.41/0.99      | ~ l1_orders_2(sK6)
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_686]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_709,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,X1)
% 3.41/0.99      | ~ l1_waybel_0(X2,X1)
% 3.41/0.99      | ~ m1_yellow_0(X0,X2)
% 3.41/0.99      | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
% 3.41/0.99      | ~ l1_struct_0(X1)
% 3.41/0.99      | ~ l1_orders_2(sK6)
% 3.41/0.99      | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) != u1_waybel_0(X1,X0)
% 3.41/0.99      | k4_waybel_9(sK5,sK6,sK7) != X0
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | sK6 != X2
% 3.41/0.99      | sK5 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_687]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_710,plain,
% 3.41/0.99      ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
% 3.41/0.99      | ~ l1_waybel_0(sK6,sK5)
% 3.41/0.99      | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
% 3.41/0.99      | ~ l1_struct_0(sK5)
% 3.41/0.99      | ~ l1_orders_2(sK6)
% 3.41/0.99      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_709]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_712,plain,
% 3.41/0.99      ( ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
% 3.41/0.99      | ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
% 3.41/0.99      | ~ l1_orders_2(sK6)
% 3.41/0.99      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_710,c_40,c_38]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_713,plain,
% 3.41/0.99      ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
% 3.41/0.99      | ~ m1_yellow_0(k4_waybel_9(sK5,sK6,sK7),sK6)
% 3.41/0.99      | ~ l1_orders_2(sK6)
% 3.41/0.99      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
% 3.41/0.99      inference(renaming,[status(thm)],[c_712]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_924,plain,
% 3.41/0.99      ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
% 3.41/0.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.41/0.99      | ~ r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 3.41/0.99      | ~ l1_orders_2(X0)
% 3.41/0.99      | ~ l1_orders_2(X1)
% 3.41/0.99      | ~ l1_orders_2(sK6)
% 3.41/0.99      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k4_waybel_9(sK5,sK6,sK7) != X0
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | sK6 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_713]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_925,plain,
% 3.41/0.99      ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
% 3.41/0.99      | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6))
% 3.41/0.99      | ~ r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6))
% 3.41/0.99      | ~ l1_orders_2(k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | ~ l1_orders_2(sK6)
% 3.41/0.99      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_924]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_941,plain,
% 3.41/0.99      ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
% 3.41/0.99      | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6))
% 3.41/0.99      | ~ r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6))
% 3.41/0.99      | ~ l1_orders_2(sK6)
% 3.41/0.99      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
% 3.41/0.99      inference(forward_subsumption_resolution,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_925,c_814]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_967,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,sK5)
% 3.41/0.99      | ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
% 3.41/0.99      | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6))
% 3.41/0.99      | ~ r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6))
% 3.41/0.99      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | sK6 != X0 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_814,c_941]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_968,plain,
% 3.41/0.99      ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
% 3.41/0.99      | ~ l1_waybel_0(sK6,sK5)
% 3.41/0.99      | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6))
% 3.41/0.99      | ~ r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6))
% 3.41/0.99      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_967]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_970,plain,
% 3.41/0.99      ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
% 3.41/0.99      | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6))
% 3.41/0.99      | ~ r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6))
% 3.41/0.99      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_968,c_38]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4463,plain,
% 3.41/0.99      ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
% 3.41/0.99      | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6))
% 3.41/0.99      | ~ r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6))
% 3.41/0.99      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7)) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_970]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5136,plain,
% 3.41/0.99      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5) != iProver_top
% 3.41/0.99      | r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6)) != iProver_top
% 3.41/0.99      | r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6)) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4463]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_46,plain,
% 3.41/0.99      ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4609,plain,
% 3.41/0.99      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5) != iProver_top
% 3.41/0.99      | r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6)) != iProver_top
% 3.41/0.99      | r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6)) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_4463]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5373,plain,
% 3.41/0.99      ( l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5) = iProver_top
% 3.41/0.99      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.41/0.99      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 3.41/0.99      | v2_struct_0(sK6) = iProver_top ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_5371]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_35,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,X1)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.41/0.99      | r1_tarski(u1_struct_0(k4_waybel_9(X1,X0,X2)),u1_struct_0(X0))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | v2_struct_0(X0)
% 3.41/0.99      | ~ l1_struct_0(X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_769,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,X1)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.41/0.99      | r1_tarski(u1_struct_0(k4_waybel_9(X1,X0,X2)),u1_struct_0(X0))
% 3.41/0.99      | v2_struct_0(X0)
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | sK5 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_35,c_40]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_770,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,sK5)
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.41/0.99      | r1_tarski(u1_struct_0(k4_waybel_9(sK5,X0,X1)),u1_struct_0(X0))
% 3.41/0.99      | v2_struct_0(X0)
% 3.41/0.99      | v2_struct_0(sK5) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_769]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_774,plain,
% 3.41/0.99      ( v2_struct_0(X0)
% 3.41/0.99      | r1_tarski(u1_struct_0(k4_waybel_9(sK5,X0,X1)),u1_struct_0(X0))
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.41/0.99      | ~ l1_waybel_0(X0,sK5) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_770,c_41]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_775,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0,sK5)
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.41/0.99      | r1_tarski(u1_struct_0(k4_waybel_9(sK5,X0,X1)),u1_struct_0(X0))
% 3.41/0.99      | v2_struct_0(X0) ),
% 3.41/0.99      inference(renaming,[status(thm)],[c_774]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4466,plain,
% 3.41/0.99      ( ~ l1_waybel_0(X0_61,sK5)
% 3.41/0.99      | ~ m1_subset_1(X0_62,u1_struct_0(X0_61))
% 3.41/0.99      | r1_tarski(u1_struct_0(k4_waybel_9(sK5,X0_61,X0_62)),u1_struct_0(X0_61))
% 3.41/0.99      | v2_struct_0(X0_61) ),
% 3.41/0.99      inference(subtyping,[status(esa)],[c_775]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5375,plain,
% 3.41/0.99      ( ~ l1_waybel_0(sK6,sK5)
% 3.41/0.99      | ~ m1_subset_1(X0_62,u1_struct_0(sK6))
% 3.41/0.99      | r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(sK6))
% 3.41/0.99      | v2_struct_0(sK6) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_4466]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5376,plain,
% 3.41/0.99      ( l1_waybel_0(sK6,sK5) != iProver_top
% 3.41/0.99      | m1_subset_1(X0_62,u1_struct_0(sK6)) != iProver_top
% 3.41/0.99      | r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(sK6)) = iProver_top
% 3.41/0.99      | v2_struct_0(sK6) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_5375]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5378,plain,
% 3.41/0.99      ( l1_waybel_0(sK6,sK5) != iProver_top
% 3.41/0.99      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 3.41/0.99      | r1_tarski(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(sK6)) = iProver_top
% 3.41/0.99      | v2_struct_0(sK6) = iProver_top ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_5376]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5591,plain,
% 3.41/0.99      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_waybel_0(sK5,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | k1_toler_1(u1_orders_2(sK6),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))) != u1_orders_2(k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | r1_tarski(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),u1_orders_2(sK6)) != iProver_top ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_5136,c_44,c_45,c_46,c_4609,c_5373,c_5378]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5542,plain,
% 3.41/0.99      ( ~ sP1(X0_62,sK5,sK6,k4_waybel_9(sK5,sK6,X0_62))
% 3.41/0.99      | sP0(k4_waybel_9(sK5,sK6,X0_62),sK6,sK5,X0_62) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_4482]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5544,plain,
% 3.41/0.99      ( ~ sP1(sK7,sK5,sK6,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | sP0(k4_waybel_9(sK5,sK6,sK7),sK6,sK5,sK7) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_5542]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5380,plain,
% 3.41/0.99      ( sP1(X0_62,sK5,sK6,k4_waybel_9(sK5,X0_61,X1_62))
% 3.41/0.99      | ~ l1_waybel_0(X0_61,sK5)
% 3.41/0.99      | ~ l1_waybel_0(sK6,sK5)
% 3.41/0.99      | ~ m1_subset_1(X1_62,u1_struct_0(X0_61))
% 3.41/0.99      | ~ m1_subset_1(X0_62,u1_struct_0(sK6))
% 3.41/0.99      | v2_struct_0(X0_61)
% 3.41/0.99      | v2_struct_0(sK6) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_4467]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5517,plain,
% 3.41/0.99      ( sP1(X0_62,sK5,sK6,k4_waybel_9(sK5,sK6,X1_62))
% 3.41/0.99      | ~ l1_waybel_0(sK6,sK5)
% 3.41/0.99      | ~ m1_subset_1(X0_62,u1_struct_0(sK6))
% 3.41/0.99      | ~ m1_subset_1(X1_62,u1_struct_0(sK6))
% 3.41/0.99      | v2_struct_0(sK6) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_5380]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5519,plain,
% 3.41/0.99      ( sP1(sK7,sK5,sK6,k4_waybel_9(sK5,sK6,sK7))
% 3.41/0.99      | ~ l1_waybel_0(sK6,sK5)
% 3.41/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK6))
% 3.41/0.99      | v2_struct_0(sK6) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_5517]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5463,plain,
% 3.41/0.99      ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,X0_62),sK5)
% 3.41/0.99      | m1_subset_1(u1_orders_2(k4_waybel_9(sK5,sK6,X0_62)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,X0_62)),u1_struct_0(k4_waybel_9(sK5,sK6,X0_62))))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_4464]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5480,plain,
% 3.41/0.99      ( ~ l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
% 3.41/0.99      | m1_subset_1(u1_orders_2(k4_waybel_9(sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK5,sK6,sK7)),u1_struct_0(k4_waybel_9(sK5,sK6,sK7))))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_5463]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5372,plain,
% 3.41/0.99      ( l1_waybel_0(k4_waybel_9(sK5,sK6,sK7),sK5)
% 3.41/0.99      | ~ l1_waybel_0(sK6,sK5)
% 3.41/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK6))
% 3.41/0.99      | v2_struct_0(sK6) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_5370]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(contradiction,plain,
% 3.41/0.99      ( $false ),
% 3.41/0.99      inference(minisat,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_9341,c_7476,c_6763,c_5688,c_5684,c_5591,c_5544,c_5519,
% 3.41/0.99                 c_5480,c_5455,c_5385,c_5372,c_37,c_38,c_39]) ).
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  ------                               Statistics
% 3.41/0.99  
% 3.41/0.99  ------ General
% 3.41/0.99  
% 3.41/0.99  abstr_ref_over_cycles:                  0
% 3.41/0.99  abstr_ref_under_cycles:                 0
% 3.41/0.99  gc_basic_clause_elim:                   0
% 3.41/0.99  forced_gc_time:                         0
% 3.41/1.00  parsing_time:                           0.012
% 3.41/1.00  unif_index_cands_time:                  0.
% 3.41/1.00  unif_index_add_time:                    0.
% 3.41/1.00  orderings_time:                         0.
% 3.41/1.00  out_proof_time:                         0.015
% 3.41/1.00  total_time:                             0.284
% 3.41/1.00  num_of_symbols:                         68
% 3.41/1.00  num_of_terms:                           8786
% 3.41/1.00  
% 3.41/1.00  ------ Preprocessing
% 3.41/1.00  
% 3.41/1.00  num_of_splits:                          0
% 3.41/1.00  num_of_split_atoms:                     0
% 3.41/1.00  num_of_reused_defs:                     0
% 3.41/1.00  num_eq_ax_congr_red:                    70
% 3.41/1.00  num_of_sem_filtered_clauses:            1
% 3.41/1.00  num_of_subtypes:                        4
% 3.41/1.00  monotx_restored_types:                  1
% 3.41/1.00  sat_num_of_epr_types:                   0
% 3.41/1.00  sat_num_of_non_cyclic_types:            0
% 3.41/1.00  sat_guarded_non_collapsed_types:        2
% 3.41/1.00  num_pure_diseq_elim:                    0
% 3.41/1.00  simp_replaced_by:                       0
% 3.41/1.00  res_preprocessed:                       177
% 3.41/1.00  prep_upred:                             0
% 3.41/1.00  prep_unflattend:                        206
% 3.41/1.00  smt_new_axioms:                         0
% 3.41/1.00  pred_elim_cands:                        10
% 3.41/1.00  pred_elim:                              7
% 3.41/1.00  pred_elim_cl:                           14
% 3.41/1.00  pred_elim_cycles:                       20
% 3.41/1.00  merged_defs:                            0
% 3.41/1.00  merged_defs_ncl:                        0
% 3.41/1.00  bin_hyper_res:                          0
% 3.41/1.00  prep_cycles:                            4
% 3.41/1.00  pred_elim_time:                         0.076
% 3.41/1.00  splitting_time:                         0.
% 3.41/1.00  sem_filter_time:                        0.
% 3.41/1.00  monotx_time:                            0.001
% 3.41/1.00  subtype_inf_time:                       0.002
% 3.41/1.00  
% 3.41/1.00  ------ Problem properties
% 3.41/1.00  
% 3.41/1.00  clauses:                                28
% 3.41/1.00  conjectures:                            4
% 3.41/1.00  epr:                                    3
% 3.41/1.00  horn:                                   22
% 3.41/1.00  ground:                                 5
% 3.41/1.00  unary:                                  5
% 3.41/1.00  binary:                                 9
% 3.41/1.00  lits:                                   84
% 3.41/1.00  lits_eq:                                13
% 3.41/1.00  fd_pure:                                0
% 3.41/1.00  fd_pseudo:                              0
% 3.41/1.00  fd_cond:                                0
% 3.41/1.00  fd_pseudo_cond:                         2
% 3.41/1.00  ac_symbols:                             0
% 3.41/1.00  
% 3.41/1.00  ------ Propositional Solver
% 3.41/1.00  
% 3.41/1.00  prop_solver_calls:                      29
% 3.41/1.00  prop_fast_solver_calls:                 2244
% 3.41/1.00  smt_solver_calls:                       0
% 3.41/1.00  smt_fast_solver_calls:                  0
% 3.41/1.00  prop_num_of_clauses:                    2330
% 3.41/1.00  prop_preprocess_simplified:             8227
% 3.41/1.00  prop_fo_subsumed:                       40
% 3.41/1.00  prop_solver_time:                       0.
% 3.41/1.00  smt_solver_time:                        0.
% 3.41/1.00  smt_fast_solver_time:                   0.
% 3.41/1.00  prop_fast_solver_time:                  0.
% 3.41/1.00  prop_unsat_core_time:                   0.
% 3.41/1.00  
% 3.41/1.00  ------ QBF
% 3.41/1.00  
% 3.41/1.00  qbf_q_res:                              0
% 3.41/1.00  qbf_num_tautologies:                    0
% 3.41/1.00  qbf_prep_cycles:                        0
% 3.41/1.00  
% 3.41/1.00  ------ BMC1
% 3.41/1.00  
% 3.41/1.00  bmc1_current_bound:                     -1
% 3.41/1.00  bmc1_last_solved_bound:                 -1
% 3.41/1.00  bmc1_unsat_core_size:                   -1
% 3.41/1.00  bmc1_unsat_core_parents_size:           -1
% 3.41/1.00  bmc1_merge_next_fun:                    0
% 3.41/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.41/1.00  
% 3.41/1.00  ------ Instantiation
% 3.41/1.00  
% 3.41/1.00  inst_num_of_clauses:                    595
% 3.41/1.00  inst_num_in_passive:                    59
% 3.41/1.00  inst_num_in_active:                     393
% 3.41/1.00  inst_num_in_unprocessed:                143
% 3.41/1.00  inst_num_of_loops:                      410
% 3.41/1.00  inst_num_of_learning_restarts:          0
% 3.41/1.00  inst_num_moves_active_passive:          13
% 3.41/1.00  inst_lit_activity:                      0
% 3.41/1.00  inst_lit_activity_moves:                0
% 3.41/1.00  inst_num_tautologies:                   0
% 3.41/1.00  inst_num_prop_implied:                  0
% 3.41/1.00  inst_num_existing_simplified:           0
% 3.41/1.00  inst_num_eq_res_simplified:             0
% 3.41/1.00  inst_num_child_elim:                    0
% 3.41/1.00  inst_num_of_dismatching_blockings:      198
% 3.41/1.00  inst_num_of_non_proper_insts:           745
% 3.41/1.00  inst_num_of_duplicates:                 0
% 3.41/1.00  inst_inst_num_from_inst_to_res:         0
% 3.41/1.00  inst_dismatching_checking_time:         0.
% 3.41/1.00  
% 3.41/1.00  ------ Resolution
% 3.41/1.00  
% 3.41/1.00  res_num_of_clauses:                     0
% 3.41/1.00  res_num_in_passive:                     0
% 3.41/1.00  res_num_in_active:                      0
% 3.41/1.00  res_num_of_loops:                       181
% 3.41/1.00  res_forward_subset_subsumed:            39
% 3.41/1.00  res_backward_subset_subsumed:           0
% 3.41/1.00  res_forward_subsumed:                   0
% 3.41/1.00  res_backward_subsumed:                  0
% 3.41/1.00  res_forward_subsumption_resolution:     3
% 3.41/1.00  res_backward_subsumption_resolution:    0
% 3.41/1.00  res_clause_to_clause_subsumption:       258
% 3.41/1.00  res_orphan_elimination:                 0
% 3.41/1.00  res_tautology_del:                      121
% 3.41/1.00  res_num_eq_res_simplified:              0
% 3.41/1.00  res_num_sel_changes:                    0
% 3.41/1.00  res_moves_from_active_to_pass:          0
% 3.41/1.00  
% 3.41/1.00  ------ Superposition
% 3.41/1.00  
% 3.41/1.00  sup_time_total:                         0.
% 3.41/1.00  sup_time_generating:                    0.
% 3.41/1.00  sup_time_sim_full:                      0.
% 3.41/1.00  sup_time_sim_immed:                     0.
% 3.41/1.00  
% 3.41/1.00  sup_num_of_clauses:                     114
% 3.41/1.00  sup_num_in_active:                      79
% 3.41/1.00  sup_num_in_passive:                     35
% 3.41/1.00  sup_num_of_loops:                       81
% 3.41/1.00  sup_fw_superposition:                   52
% 3.41/1.00  sup_bw_superposition:                   59
% 3.41/1.00  sup_immediate_simplified:               23
% 3.41/1.00  sup_given_eliminated:                   0
% 3.41/1.00  comparisons_done:                       0
% 3.41/1.00  comparisons_avoided:                    0
% 3.41/1.00  
% 3.41/1.00  ------ Simplifications
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  sim_fw_subset_subsumed:                 5
% 3.41/1.00  sim_bw_subset_subsumed:                 1
% 3.41/1.00  sim_fw_subsumed:                        3
% 3.41/1.00  sim_bw_subsumed:                        0
% 3.41/1.00  sim_fw_subsumption_res:                 2
% 3.41/1.00  sim_bw_subsumption_res:                 0
% 3.41/1.00  sim_tautology_del:                      0
% 3.41/1.00  sim_eq_tautology_del:                   8
% 3.41/1.00  sim_eq_res_simp:                        1
% 3.41/1.00  sim_fw_demodulated:                     9
% 3.41/1.00  sim_bw_demodulated:                     3
% 3.41/1.00  sim_light_normalised:                   10
% 3.41/1.00  sim_joinable_taut:                      0
% 3.41/1.00  sim_joinable_simp:                      0
% 3.41/1.00  sim_ac_normalised:                      0
% 3.41/1.00  sim_smt_subsumption:                    0
% 3.41/1.00  
%------------------------------------------------------------------------------
