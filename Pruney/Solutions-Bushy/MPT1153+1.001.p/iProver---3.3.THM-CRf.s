%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1153+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:02 EST 2020

% Result     : Theorem 1.12s
% Output     : CNFRefutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 381 expanded)
%              Number of clauses        :   63 (  91 expanded)
%              Number of leaves         :   12 ( 126 expanded)
%              Depth                    :   16
%              Number of atoms          :  503 (2818 expanded)
%              Number of equality atoms :   53 (  80 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                    & r2_hidden(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k1_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k1_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X1,k1_orders_2(X0,X2))
          & r2_hidden(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,k1_orders_2(X0,sK4))
        & r2_hidden(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k1_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( r2_hidden(sK3,k1_orders_2(X0,X2))
            & r2_hidden(sK3,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( r2_hidden(X1,k1_orders_2(X0,X2))
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k1_orders_2(sK2,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( r2_hidden(sK3,k1_orders_2(sK2,sK4))
    & r2_hidden(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f24,f23,f22])).

fof(f39,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X4,X3)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X6,X5)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f17])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK1(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK1(X0,X1,X2) = X0
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK0(X1,X2,X3),X3)
        & r2_hidden(sK0(X1,X2,X3),X2)
        & m1_subset_1(sK0(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK0(X1,X2,X3),X3)
                & r2_hidden(sK0(X1,X2,X3),X2)
                & m1_subset_1(sK0(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK1(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK1(X0,X1,X2) = X0
            & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f29,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,X6,sK1(X0,X1,X2))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( sK1(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    r2_hidden(sK3,k1_orders_2(sK2,sK4)) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_734,plain,
    ( ~ r2_hidden(X0_46,X1_46)
    | r2_hidden(X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_1195,plain,
    ( r2_hidden(X0_46,X1_46)
    | ~ r2_hidden(sK3,sK4)
    | X1_46 != sK4
    | X0_46 != sK3 ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_1214,plain,
    ( r2_hidden(X0_46,sK4)
    | ~ r2_hidden(sK3,sK4)
    | X0_46 != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1195])).

cnf(c_1410,plain,
    ( r2_hidden(sK1(X0_46,sK2,sK4),sK4)
    | ~ r2_hidden(sK3,sK4)
    | sK1(X0_46,sK2,sK4) != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_1412,plain,
    ( r2_hidden(sK1(sK3,sK2,sK4),sK4)
    | ~ r2_hidden(sK3,sK4)
    | sK1(sK3,sK2,sK4) != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1410])).

cnf(c_7,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_491,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_492,plain,
    ( ~ r2_orders_2(sK2,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_713,plain,
    ( ~ r2_orders_2(sK2,X0_46,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_492])).

cnf(c_727,plain,
    ( ~ r2_orders_2(sK2,X0_46,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_713])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_728,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_713])).

cnf(c_726,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_713])).

cnf(c_775,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_816,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ r2_orders_2(sK2,X0_46,X0_46) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_12,c_728,c_775])).

cnf(c_817,plain,
    ( ~ r2_orders_2(sK2,X0_46,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_816])).

cnf(c_1283,plain,
    ( ~ r2_orders_2(sK2,sK1(X0_46,sK2,sK4),sK1(X0_46,sK2,sK4))
    | ~ m1_subset_1(sK1(X0_46,sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_1289,plain,
    ( ~ r2_orders_2(sK2,sK1(sK3,sK2,sK4),sK1(sK3,sK2,sK4))
    | ~ m1_subset_1(sK1(sK3,sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1283])).

cnf(c_4,plain,
    ( r2_orders_2(X0,X1,sK1(X2,X0,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_299,plain,
    ( r2_orders_2(X0,X1,sK1(X2,X0,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_300,plain,
    ( r2_orders_2(sK2,X0,sK1(X1,sK2,X2))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK2,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_304,plain,
    ( r2_orders_2(sK2,X0,sK1(X1,sK2,X2))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK2,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_300,c_17,c_16,c_15,c_13])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_320,plain,
    ( r2_orders_2(sK2,X0,sK1(X1,sK2,X2))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK2,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_304,c_8])).

cnf(c_720,plain,
    ( r2_orders_2(sK2,X0_46,sK1(X1_46,sK2,X2_46))
    | ~ r2_hidden(X0_46,X2_46)
    | ~ r2_hidden(X1_46,a_2_0_orders_2(sK2,X2_46))
    | ~ m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_320])).

cnf(c_1167,plain,
    ( r2_orders_2(sK2,X0_46,sK1(X1_46,sK2,sK4))
    | ~ r2_hidden(X1_46,a_2_0_orders_2(sK2,sK4))
    | ~ r2_hidden(X0_46,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1282,plain,
    ( r2_orders_2(sK2,sK1(X0_46,sK2,sK4),sK1(X0_46,sK2,sK4))
    | ~ r2_hidden(X0_46,a_2_0_orders_2(sK2,sK4))
    | ~ r2_hidden(sK1(X0_46,sK2,sK4),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_1285,plain,
    ( r2_orders_2(sK2,sK1(sK3,sK2,sK4),sK1(sK3,sK2,sK4))
    | ~ r2_hidden(sK1(sK3,sK2,sK4),sK4)
    | ~ r2_hidden(sK3,a_2_0_orders_2(sK2,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_1190,plain,
    ( r2_hidden(X0_46,X1_46)
    | ~ r2_hidden(sK3,k1_orders_2(sK2,sK4))
    | X1_46 != k1_orders_2(sK2,sK4)
    | X0_46 != sK3 ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_1232,plain,
    ( r2_hidden(X0_46,a_2_0_orders_2(sK2,sK4))
    | ~ r2_hidden(sK3,k1_orders_2(sK2,sK4))
    | X0_46 != sK3
    | a_2_0_orders_2(sK2,sK4) != k1_orders_2(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1190])).

cnf(c_1234,plain,
    ( r2_hidden(sK3,a_2_0_orders_2(sK2,sK4))
    | ~ r2_hidden(sK3,k1_orders_2(sK2,sK4))
    | a_2_0_orders_2(sK2,sK4) != k1_orders_2(sK2,sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_730,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1215,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_373,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1(X0,X1,X2) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_374,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | sK1(X0,sK2,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_378,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(X0,sK2,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_374,c_17,c_16,c_15,c_13])).

cnf(c_717,plain,
    ( ~ r2_hidden(X0_46,a_2_0_orders_2(sK2,X1_46))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(X0_46,sK2,X1_46) = X0_46 ),
    inference(subtyping,[status(esa)],[c_378])).

cnf(c_1148,plain,
    ( ~ r2_hidden(X0_46,a_2_0_orders_2(sK2,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(X0_46,sK2,sK4) = X0_46 ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_1150,plain,
    ( ~ r2_hidden(sK3,a_2_0_orders_2(sK2,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK3,sK2,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_352,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_353,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(X0,sK2,X1),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_357,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(X0,sK2,X1),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_17,c_16,c_15,c_13])).

cnf(c_718,plain,
    ( ~ r2_hidden(X0_46,a_2_0_orders_2(sK2,X1_46))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(X0_46,sK2,X1_46),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_357])).

cnf(c_1138,plain,
    ( ~ r2_hidden(X0_46,a_2_0_orders_2(sK2,sK4))
    | m1_subset_1(sK1(X0_46,sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_1140,plain,
    ( ~ r2_hidden(sK3,a_2_0_orders_2(sK2,sK4))
    | m1_subset_1(sK1(sK3,sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | a_2_0_orders_2(sK2,X0) = k1_orders_2(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | a_2_0_orders_2(sK2,X0) = k1_orders_2(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_443,c_17,c_16,c_15,c_13])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | a_2_0_orders_2(sK2,X0_46) = k1_orders_2(sK2,X0_46) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_1135,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | a_2_0_orders_2(sK2,sK4) = k1_orders_2(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_741,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK3,k1_orders_2(sK2,sK4)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1412,c_1289,c_1285,c_1234,c_1215,c_1150,c_1140,c_1135,c_741,c_9,c_10,c_11])).


%------------------------------------------------------------------------------
