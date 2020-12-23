%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1627+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:00 EST 2020

% Result     : Theorem 0.81s
% Output     : CNFRefutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 363 expanded)
%              Number of clauses        :   37 (  60 expanded)
%              Number of leaves         :    7 ( 130 expanded)
%              Depth                    :   17
%              Number of atoms          :  427 (4314 expanded)
%              Number of equality atoms :   68 ( 751 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_waybel_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v1_waybel_0(X2,X1) )
             => ( r1_yellow_0(X0,X2)
               => ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                    & r1_yellow_0(X1,X2) )
                  | k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_waybel_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_0(X2,X1) )
               => ( r1_yellow_0(X0,X2)
                 => ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                      & r1_yellow_0(X1,X2) )
                    | k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v1_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v4_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v1_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v4_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
            | ~ r1_yellow_0(X1,X2) )
          & k1_xboole_0 != X2
          & r1_yellow_0(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v1_waybel_0(X2,X1) )
     => ( ( k1_yellow_0(X0,sK3) != k1_yellow_0(X1,sK3)
          | ~ r1_yellow_0(X1,sK3) )
        & k1_xboole_0 != sK3
        & r1_yellow_0(X0,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1)))
        & v1_waybel_0(sK3,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v1_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v4_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k1_yellow_0(sK2,X2) != k1_yellow_0(X0,X2)
              | ~ r1_yellow_0(sK2,X2) )
            & k1_xboole_0 != X2
            & r1_yellow_0(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
            & v1_waybel_0(X2,sK2) )
        & m1_yellow_0(sK2,X0)
        & v4_waybel_0(sK2,X0)
        & v4_yellow_0(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                  | ~ r1_yellow_0(X1,X2) )
                & k1_xboole_0 != X2
                & r1_yellow_0(X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v1_waybel_0(X2,X1) )
            & m1_yellow_0(X1,X0)
            & v4_waybel_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(sK1,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r1_yellow_0(sK1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v1_waybel_0(X2,X1) )
          & m1_yellow_0(X1,sK1)
          & v4_waybel_0(X1,sK1)
          & v4_yellow_0(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ( k1_yellow_0(sK1,sK3) != k1_yellow_0(sK2,sK3)
      | ~ r1_yellow_0(sK2,sK3) )
    & k1_xboole_0 != sK3
    & r1_yellow_0(sK1,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_waybel_0(sK3,sK2)
    & m1_yellow_0(sK2,sK1)
    & v4_waybel_0(sK2,sK1)
    & v4_yellow_0(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_orders_2(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f10,f17,f16,f15])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & r1_yellow_0(X0,X2) )
               => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                  & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X1,X2)
      | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    v4_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    v4_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    r1_yellow_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_0(X2,X1) )
               => ( r1_yellow_0(X0,X2)
                 => ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                    | k1_xboole_0 = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                | k1_xboole_0 = X2
                | ~ r1_yellow_0(X0,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_0(X2,X1) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                | k1_xboole_0 = X2
                | ~ r1_yellow_0(X0,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_0(X2,X1) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & k1_xboole_0 != X2
                  & r1_yellow_0(X0,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_0(X2,X1) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  | k1_xboole_0 = X2
                  | ~ r1_yellow_0(X0,X2)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v1_waybel_0(X2,X1) )
              | ~ v4_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & k1_xboole_0 != X2
                  & r1_yellow_0(X0,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_0(X2,X1) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),u1_struct_0(X1))
                  | k1_xboole_0 = X3
                  | ~ r1_yellow_0(X0,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v1_waybel_0(X3,X1) )
              | ~ v4_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
          & k1_xboole_0 != X2
          & r1_yellow_0(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v1_waybel_0(X2,X1) )
     => ( ~ r2_hidden(k1_yellow_0(X0,sK0(X0,X1)),u1_struct_0(X1))
        & k1_xboole_0 != sK0(X0,X1)
        & r1_yellow_0(X0,sK0(X0,X1))
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
        & v1_waybel_0(sK0(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_0(X1,X0)
              | ( ~ r2_hidden(k1_yellow_0(X0,sK0(X0,X1)),u1_struct_0(X1))
                & k1_xboole_0 != sK0(X0,X1)
                & r1_yellow_0(X0,sK0(X0,X1))
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
                & v1_waybel_0(sK0(X0,X1),X1) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),u1_struct_0(X1))
                  | k1_xboole_0 = X3
                  | ~ r1_yellow_0(X0,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v1_waybel_0(X3,X1) )
              | ~ v4_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_yellow_0(X0,X3),u1_struct_0(X1))
      | k1_xboole_0 = X3
      | ~ r1_yellow_0(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_waybel_0(X3,X1)
      | ~ v4_waybel_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    v1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,
    ( k1_yellow_0(sK1,sK3) != k1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( ~ v4_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_yellow_0(X1,X2)
    | r1_yellow_0(X0,X2)
    | ~ m1_yellow_0(X0,X1)
    | ~ r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X0))
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_15,negated_conjecture,
    ( v4_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_yellow_0(X2,X0)
    | r1_yellow_0(X1,X0)
    | ~ m1_yellow_0(X1,X2)
    | ~ r2_hidden(k1_yellow_0(X2,X0),u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X2)
    | sK2 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_204,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_yellow_0(sK2,X0)
    | ~ r1_yellow_0(sK1,X0)
    | ~ m1_yellow_0(sK2,sK1)
    | ~ r2_hidden(k1_yellow_0(sK1,X0),u1_struct_0(sK2))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_18,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,negated_conjecture,
    ( m1_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_208,plain,
    ( ~ r1_yellow_0(sK1,X0)
    | r1_yellow_0(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(k1_yellow_0(sK1,X0),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_204,c_19,c_18,c_17,c_16,c_13])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_yellow_0(sK2,X0)
    | ~ r1_yellow_0(sK1,X0)
    | ~ r2_hidden(k1_yellow_0(sK1,X0),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_452,plain,
    ( r1_yellow_0(sK2,X0)
    | ~ r1_yellow_0(sK1,X0)
    | ~ r2_hidden(k1_yellow_0(sK1,X0),u1_struct_0(sK2))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_209])).

cnf(c_453,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK1,sK3)
    | ~ r2_hidden(k1_yellow_0(sK1,sK3),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_14,negated_conjecture,
    ( v4_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,negated_conjecture,
    ( r1_yellow_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_9,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_yellow_0(X2,X0)
    | ~ m1_yellow_0(X1,X2)
    | r2_hidden(k1_yellow_0(X2,X0),u1_struct_0(X1))
    | ~ v4_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_12,negated_conjecture,
    ( v1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_yellow_0(X2,X0)
    | ~ m1_yellow_0(X1,X2)
    | r2_hidden(k1_yellow_0(X2,X0),u1_struct_0(X1))
    | ~ v4_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | sK2 != X1
    | sK3 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

cnf(c_303,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_yellow_0(X0,sK3)
    | ~ m1_yellow_0(sK2,X0)
    | r2_hidden(k1_yellow_0(X0,sK3),u1_struct_0(sK2))
    | ~ v4_waybel_0(sK2,X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_305,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_yellow_0(sK1,sK3)
    | ~ m1_yellow_0(sK2,sK1)
    | r2_hidden(k1_yellow_0(sK1,sK3),u1_struct_0(sK2))
    | ~ v4_waybel_0(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_455,plain,
    ( r1_yellow_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_19,c_17,c_14,c_13,c_11,c_10,c_9,c_305])).

cnf(c_8,negated_conjecture,
    ( ~ r1_yellow_0(sK2,sK3)
    | k1_yellow_0(sK1,sK3) != k1_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_465,plain,
    ( k1_yellow_0(sK1,sK3) != k1_yellow_0(sK2,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_455,c_8])).

cnf(c_470,plain,
    ( k1_yellow_0(sK1,sK3) != k1_yellow_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_465])).

cnf(c_6,plain,
    ( ~ v4_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_yellow_0(X0,X1)
    | ~ r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X0))
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_yellow_0(X2,X0)
    | ~ m1_yellow_0(X1,X2)
    | ~ r2_hidden(k1_yellow_0(X2,X0),u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X2)
    | k1_yellow_0(X1,X0) = k1_yellow_0(X2,X0)
    | sK2 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_yellow_0(sK1,X0)
    | ~ m1_yellow_0(sK2,sK1)
    | ~ r2_hidden(k1_yellow_0(sK1,X0),u1_struct_0(sK2))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | k1_yellow_0(sK2,X0) = k1_yellow_0(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_232,plain,
    ( ~ r1_yellow_0(sK1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(k1_yellow_0(sK1,X0),u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = k1_yellow_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_19,c_18,c_17,c_16,c_13])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_yellow_0(sK1,X0)
    | ~ r2_hidden(k1_yellow_0(sK1,X0),u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = k1_yellow_0(sK1,X0) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_444,plain,
    ( ~ r1_yellow_0(sK1,X0)
    | ~ r2_hidden(k1_yellow_0(sK1,X0),u1_struct_0(sK2))
    | k1_yellow_0(sK2,X0) = k1_yellow_0(sK1,X0)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_233])).

cnf(c_445,plain,
    ( ~ r1_yellow_0(sK1,sK3)
    | ~ r2_hidden(k1_yellow_0(sK1,sK3),u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK3) = k1_yellow_0(sK1,sK3) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_447,plain,
    ( k1_yellow_0(sK2,sK3) = k1_yellow_0(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_19,c_17,c_14,c_13,c_11,c_10,c_9,c_305])).

cnf(c_471,plain,
    ( k1_yellow_0(sK2,sK3) = k1_yellow_0(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_481,plain,
    ( k1_yellow_0(sK1,sK3) != k1_yellow_0(sK1,sK3) ),
    inference(light_normalisation,[status(thm)],[c_470,c_471])).

cnf(c_482,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_481])).


%------------------------------------------------------------------------------
