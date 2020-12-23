%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1688+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:11 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 841 expanded)
%              Number of clauses        :   82 ( 186 expanded)
%              Number of leaves         :   14 ( 303 expanded)
%              Depth                    :   20
%              Number of atoms          :  719 (9633 expanded)
%              Number of equality atoms :  164 (1028 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v23_waybel_0(X2,X0,X1)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( k2_funct_1(X2) = X3
                     => v23_waybel_0(X3,X1,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v23_waybel_0(X2,X0,X1)
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                        & v1_funct_1(X3) )
                     => ( k2_funct_1(X2) = X3
                       => v23_waybel_0(X3,X1,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v23_waybel_0(X3,X1,X0)
                  & k2_funct_1(X2) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v23_waybel_0(X3,X1,X0)
                  & k2_funct_1(X2) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ v23_waybel_0(X3,X1,X0)
          & k2_funct_1(X2) = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ~ v23_waybel_0(sK5,X1,X0)
        & k2_funct_1(X2) = sK5
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v23_waybel_0(X3,X1,X0)
              & k2_funct_1(X2) = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & v23_waybel_0(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ~ v23_waybel_0(X3,X1,X0)
            & k2_funct_1(sK4) = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & v23_waybel_0(sK4,X0,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v23_waybel_0(X3,X1,X0)
                  & k2_funct_1(X2) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v23_waybel_0(X3,sK3,X0)
                & k2_funct_1(X2) = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & v23_waybel_0(X2,X0,sK3)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_orders_2(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v23_waybel_0(X3,X1,X0)
                    & k2_funct_1(X2) = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & v23_waybel_0(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v23_waybel_0(X3,X1,sK2)
                  & k2_funct_1(X2) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK2))
                  & v1_funct_1(X3) )
              & v23_waybel_0(X2,sK2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ v23_waybel_0(sK5,sK3,sK2)
    & k2_funct_1(sK4) = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & v23_waybel_0(sK4,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_orders_2(sK3)
    & ~ v2_struct_0(sK3)
    & l1_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f15,f28,f27,f26,f25])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    v23_waybel_0(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v23_waybel_0(X2,X0,X1)
      <=> ( ? [X3] :
              ( v5_orders_3(X3,X1,X0)
              & k2_funct_1(X2) = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & v5_orders_3(X2,X0,X1)
          & v2_funct_1(X2) ) )
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( v23_waybel_0(X2,X0,X1)
          | ! [X3] :
              ( ~ v5_orders_3(X3,X1,X0)
              | k2_funct_1(X2) != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X3) )
          | ~ v5_orders_3(X2,X0,X1)
          | ~ v2_funct_1(X2) )
        & ( ( ? [X3] :
                ( v5_orders_3(X3,X1,X0)
                & k2_funct_1(X2) = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & v5_orders_3(X2,X0,X1)
            & v2_funct_1(X2) )
          | ~ v23_waybel_0(X2,X0,X1) ) )
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( v23_waybel_0(X2,X0,X1)
          | ! [X3] :
              ( ~ v5_orders_3(X3,X1,X0)
              | k2_funct_1(X2) != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X3) )
          | ~ v5_orders_3(X2,X0,X1)
          | ~ v2_funct_1(X2) )
        & ( ( ? [X3] :
                ( v5_orders_3(X3,X1,X0)
                & k2_funct_1(X2) = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & v5_orders_3(X2,X0,X1)
            & v2_funct_1(X2) )
          | ~ v23_waybel_0(X2,X0,X1) ) )
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( v23_waybel_0(X2,X0,X1)
          | ! [X3] :
              ( ~ v5_orders_3(X3,X1,X0)
              | k2_funct_1(X2) != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X3) )
          | ~ v5_orders_3(X2,X0,X1)
          | ~ v2_funct_1(X2) )
        & ( ( ? [X4] :
                ( v5_orders_3(X4,X1,X0)
                & k2_funct_1(X2) = X4
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & v5_orders_3(X2,X0,X1)
            & v2_funct_1(X2) )
          | ~ v23_waybel_0(X2,X0,X1) ) )
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( v5_orders_3(X4,X1,X0)
          & k2_funct_1(X2) = X4
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( v5_orders_3(sK1(X0,X1,X2),X1,X0)
        & k2_funct_1(X2) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK1(X0,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( v23_waybel_0(X2,X0,X1)
          | ! [X3] :
              ( ~ v5_orders_3(X3,X1,X0)
              | k2_funct_1(X2) != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X3) )
          | ~ v5_orders_3(X2,X0,X1)
          | ~ v2_funct_1(X2) )
        & ( ( v5_orders_3(sK1(X0,X1,X2),X1,X0)
            & k2_funct_1(X2) = sK1(X0,X1,X2)
            & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(sK1(X0,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(sK1(X0,X1,X2))
            & v5_orders_3(X2,X0,X1)
            & v2_funct_1(X2) )
          | ~ v23_waybel_0(X2,X0,X1) ) )
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( ~ ( ~ v2_struct_0(X1)
                      & ~ v2_struct_0(X0) )
                 => ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) ) )
                & ~ ( ~ ( v23_waybel_0(X2,X0,X1)
                      <=> ( ? [X3] :
                              ( v5_orders_3(X3,X1,X0)
                              & k2_funct_1(X2) = X3
                              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                              & v1_funct_1(X3) )
                          & v5_orders_3(X2,X0,X1)
                          & v2_funct_1(X2) ) )
                    & ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( ? [X3] :
                          ( v5_orders_3(X3,X1,X0)
                          & k2_funct_1(X2) = X3
                          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X3) )
                      & v5_orders_3(X2,X0,X1)
                      & v2_funct_1(X2) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( ? [X3] :
                          ( v5_orders_3(X3,X1,X0)
                          & k2_funct_1(X2) = X3
                          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X3) )
                      & v5_orders_3(X2,X0,X1)
                      & v2_funct_1(X2) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & sP0(X0,X1,X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f9,f16])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( v23_waybel_0(X2,X0,X1)
                      | ~ v2_struct_0(X1)
                      | ~ v2_struct_0(X0) )
                    & ( ( v2_struct_0(X1)
                        & v2_struct_0(X0) )
                      | ~ v23_waybel_0(X2,X0,X1) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & sP0(X0,X1,X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( v23_waybel_0(X2,X0,X1)
                      | ~ v2_struct_0(X1)
                      | ~ v2_struct_0(X0) )
                    & ( ( v2_struct_0(X1)
                        & v2_struct_0(X0) )
                      | ~ v23_waybel_0(X2,X0,X1) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & sP0(X0,X1,X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f47,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    k2_funct_1(sK4) = sK5 ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( v23_waybel_0(X2,X0,X1)
      | ~ v5_orders_3(X3,X1,X0)
      | k2_funct_1(X2) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ v5_orders_3(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v23_waybel_0(X2,X0,X1)
      | ~ v5_orders_3(k2_funct_1(X2),X1,X0)
      | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v5_orders_3(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f38])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f46,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = sK1(X0,X1,X2)
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(sK1(X0,X1,X2),X1,X0)
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(X2,X0,X1)
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    ~ v23_waybel_0(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_5851,plain,
    ( ~ v5_orders_3(X0_48,X0_47,X1_47)
    | v5_orders_3(X1_48,X0_47,X1_47)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_6747,plain,
    ( v5_orders_3(X0_48,sK3,sK2)
    | ~ v5_orders_3(sK1(sK2,sK3,sK4),sK3,sK2)
    | X0_48 != sK1(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_5851])).

cnf(c_7745,plain,
    ( ~ v5_orders_3(sK1(sK2,sK3,sK4),sK3,sK2)
    | v5_orders_3(sK5,sK3,sK2)
    | sK5 != sK1(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_6747])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_5823,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_6363,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5823])).

cnf(c_23,negated_conjecture,
    ( v23_waybel_0(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_5824,negated_conjecture,
    ( v23_waybel_0(sK4,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_6362,plain,
    ( v23_waybel_0(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5824])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ v23_waybel_0(X2,X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_funct_1(X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5836,plain,
    ( ~ sP0(X0_47,X1_47,X0_48)
    | ~ v23_waybel_0(X0_48,X0_47,X1_47)
    | v2_struct_0(X1_47)
    | v2_struct_0(X0_47)
    | v2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_6351,plain,
    ( sP0(X0_47,X1_47,X0_48) != iProver_top
    | v23_waybel_0(X0_48,X0_47,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_funct_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5836])).

cnf(c_7217,plain,
    ( sP0(sK2,sK3,sK4) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6362,c_6351])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_32,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_34,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_36,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2831,plain,
    ( ~ sP0(X0,X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_funct_1(X2)
    | sK4 != X2
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_2832,plain,
    ( ~ sP0(sK2,sK3,sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_2831])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2834,plain,
    ( ~ sP0(sK2,sK3,sK4)
    | v2_funct_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2832,c_30,c_28])).

cnf(c_2836,plain,
    ( sP0(sK2,sK3,sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2834])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5832,plain,
    ( sP0(X0_47,X1_47,X0_48)
    | ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | ~ l1_orders_2(X1_47)
    | ~ l1_orders_2(X0_47)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_6661,plain,
    ( sP0(sK2,sK3,sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_orders_2(sK2)
    | ~ l1_orders_2(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5832])).

cnf(c_6662,plain,
    ( sP0(sK2,sK3,sK4) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_orders_2(sK2) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6661])).

cnf(c_7386,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7217,c_32,c_34,c_35,c_36,c_37,c_2836,c_6662])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5830,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_6357,plain,
    ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5830])).

cnf(c_7391,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7386,c_6357])).

cnf(c_19,negated_conjecture,
    ( k2_funct_1(sK4) = sK5 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_5828,negated_conjecture,
    ( k2_funct_1(sK4) = sK5 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_7392,plain,
    ( k2_funct_1(sK5) = sK4
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7391,c_5828])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5844,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_6632,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5844])).

cnf(c_6633,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6632])).

cnf(c_7455,plain,
    ( k2_funct_1(sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7392,c_35,c_37,c_6633])).

cnf(c_1,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v5_orders_3(X2,X0,X1)
    | ~ v5_orders_3(k2_funct_1(X2),X1,X0)
    | v23_waybel_0(X2,X0,X1)
    | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(k2_funct_1(X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5843,plain,
    ( ~ sP0(X0_47,X1_47,X0_48)
    | ~ v1_funct_2(k2_funct_1(X0_48),u1_struct_0(X1_47),u1_struct_0(X0_47))
    | ~ v5_orders_3(X0_48,X0_47,X1_47)
    | ~ v5_orders_3(k2_funct_1(X0_48),X1_47,X0_47)
    | v23_waybel_0(X0_48,X0_47,X1_47)
    | ~ m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_47),u1_struct_0(X0_47))))
    | v2_struct_0(X1_47)
    | v2_struct_0(X0_47)
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6344,plain,
    ( sP0(X0_47,X1_47,X0_48) != iProver_top
    | v1_funct_2(k2_funct_1(X0_48),u1_struct_0(X1_47),u1_struct_0(X0_47)) != iProver_top
    | v5_orders_3(X0_48,X0_47,X1_47) != iProver_top
    | v5_orders_3(k2_funct_1(X0_48),X1_47,X0_47) != iProver_top
    | v23_waybel_0(X0_48,X0_47,X1_47) = iProver_top
    | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_47),u1_struct_0(X0_47)))) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(X0_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5843])).

cnf(c_7459,plain,
    ( sP0(X0_47,X1_47,sK5) != iProver_top
    | v1_funct_2(k2_funct_1(sK5),u1_struct_0(X1_47),u1_struct_0(X0_47)) != iProver_top
    | v5_orders_3(k2_funct_1(sK5),X1_47,X0_47) != iProver_top
    | v5_orders_3(sK5,X0_47,X1_47) != iProver_top
    | v23_waybel_0(sK5,X0_47,X1_47) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_47),u1_struct_0(X0_47)))) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_funct_1(sK5) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7455,c_6344])).

cnf(c_7479,plain,
    ( sP0(X0_47,X1_47,sK5) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(X1_47),u1_struct_0(X0_47)) != iProver_top
    | v5_orders_3(sK4,X1_47,X0_47) != iProver_top
    | v5_orders_3(sK5,X0_47,X1_47) != iProver_top
    | v23_waybel_0(sK5,X0_47,X1_47) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_47),u1_struct_0(X0_47)))) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7459,c_7455])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_5831,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(k2_funct_1(X0_48))
    | ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_6356,plain,
    ( v2_funct_1(X0_48) != iProver_top
    | v2_funct_1(k2_funct_1(X0_48)) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5831])).

cnf(c_6962,plain,
    ( v2_funct_1(sK4) != iProver_top
    | v2_funct_1(sK5) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5828,c_6356])).

cnf(c_7579,plain,
    ( sP0(X0_47,X1_47,sK5) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(X1_47),u1_struct_0(X0_47)) != iProver_top
    | v5_orders_3(sK4,X1_47,X0_47) != iProver_top
    | v5_orders_3(sK5,X0_47,X1_47) != iProver_top
    | v23_waybel_0(sK5,X0_47,X1_47) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_47),u1_struct_0(X0_47)))) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7479,c_32,c_34,c_35,c_36,c_37,c_2836,c_6633,c_6662,c_6962])).

cnf(c_7593,plain,
    ( sP0(sK3,sK2,sK5) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_orders_3(sK4,sK2,sK3) != iProver_top
    | v5_orders_3(sK5,sK3,sK2) != iProver_top
    | v23_waybel_0(sK5,sK3,sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6363,c_7579])).

cnf(c_7594,plain,
    ( ~ sP0(sK3,sK2,sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_orders_3(sK4,sK2,sK3)
    | ~ v5_orders_3(sK5,sK3,sK2)
    | v23_waybel_0(sK5,sK3,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7593])).

cnf(c_5847,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_6769,plain,
    ( X0_48 != X1_48
    | sK5 != X1_48
    | sK5 = X0_48 ),
    inference(instantiation,[status(thm)],[c_5847])).

cnf(c_7227,plain,
    ( X0_48 != k2_funct_1(sK4)
    | sK5 = X0_48
    | sK5 != k2_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6769])).

cnf(c_7331,plain,
    ( sK1(sK2,sK3,sK4) != k2_funct_1(sK4)
    | sK5 = sK1(sK2,sK3,sK4)
    | sK5 != k2_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7227])).

cnf(c_6897,plain,
    ( X0_48 != sK5
    | sK5 = X0_48
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_6769])).

cnf(c_7162,plain,
    ( k2_funct_1(sK4) != sK5
    | sK5 = k2_funct_1(sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_6897])).

cnf(c_5846,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_6898,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_5846])).

cnf(c_3,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ v23_waybel_0(X2,X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK1(X0,X1,X2) = k2_funct_1(X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_5841,plain,
    ( ~ sP0(X0_47,X1_47,X0_48)
    | ~ v23_waybel_0(X0_48,X0_47,X1_47)
    | v2_struct_0(X1_47)
    | v2_struct_0(X0_47)
    | sK1(X0_47,X1_47,X0_48) = k2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_6682,plain,
    ( ~ sP0(sK2,sK3,sK4)
    | ~ v23_waybel_0(sK4,sK2,sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | sK1(sK2,sK3,sK4) = k2_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5841])).

cnf(c_6658,plain,
    ( sP0(sK3,sK2,sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_orders_2(sK2)
    | ~ l1_orders_2(sK3)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_5832])).

cnf(c_2,plain,
    ( ~ sP0(X0,X1,X2)
    | v5_orders_3(sK1(X0,X1,X2),X1,X0)
    | ~ v23_waybel_0(X2,X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2915,plain,
    ( ~ sP0(X0,X1,X2)
    | v5_orders_3(sK1(X0,X1,X2),X1,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | sK4 != X2
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_23])).

cnf(c_2916,plain,
    ( ~ sP0(sK2,sK3,sK4)
    | v5_orders_3(sK1(sK2,sK3,sK4),sK3,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_2915])).

cnf(c_2918,plain,
    ( ~ sP0(sK2,sK3,sK4)
    | v5_orders_3(sK1(sK2,sK3,sK4),sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2916,c_30,c_28])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2)
    | v5_orders_3(X2,X0,X1)
    | ~ v23_waybel_0(X2,X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2845,plain,
    ( ~ sP0(X0,X1,X2)
    | v5_orders_3(X2,X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | sK4 != X2
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_2846,plain,
    ( ~ sP0(sK2,sK3,sK4)
    | v5_orders_3(sK4,sK2,sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_2845])).

cnf(c_2848,plain,
    ( ~ sP0(sK2,sK3,sK4)
    | v5_orders_3(sK4,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2846,c_30,c_28])).

cnf(c_18,negated_conjecture,
    ( ~ v23_waybel_0(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7745,c_7594,c_7331,c_7162,c_6898,c_6682,c_6661,c_6658,c_5828,c_2918,c_2848,c_18,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30])).


%------------------------------------------------------------------------------
