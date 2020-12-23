%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1588+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:58 EST 2020

% Result     : Theorem 0.57s
% Output     : CNFRefutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 262 expanded)
%              Number of clauses        :   49 (  57 expanded)
%              Number of leaves         :   10 ( 101 expanded)
%              Depth                    :   15
%              Number of atoms          :  378 (2659 expanded)
%              Number of equality atoms :   72 ( 309 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                      & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                   => ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) = k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                      & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ( ( r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                        & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                     => ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) = k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                        & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
            | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
          & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
          & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,sK3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,sK3))
          | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,sK3)) )
        & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,sK3)),u1_struct_0(X1))
        & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,sK3))
        & m1_subset_1(sK3,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
              & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
              & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),sK2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),sK2,X3))
              | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),sK2,X3)) )
            & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),sK2,X3)),u1_struct_0(X1))
            & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),sK2,X3))
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK2,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X2,X3)) != k1_yellow_0(X0,k7_domain_1(u1_struct_0(sK1),X2,X3))
                  | ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X2,X3)) )
                & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(sK1),X2,X3)),u1_struct_0(sK1))
                & r1_yellow_0(X0,k7_domain_1(u1_struct_0(sK1),X2,X3))
                & m1_subset_1(X3,u1_struct_0(sK1)) )
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & m1_yellow_0(sK1,X0)
        & v4_yellow_0(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                      | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                    & r2_hidden(k1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                    & r1_yellow_0(X0,k7_domain_1(u1_struct_0(X1),X2,X3))
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(X1),X2,X3)) != k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
                    | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) )
                  & r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(X1),X2,X3)),u1_struct_0(X1))
                  & r1_yellow_0(sK0,k7_domain_1(u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,sK0)
          & v4_yellow_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
      | ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )
    & r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
    & r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & m1_yellow_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f16,f15,f14,f13])).

fof(f31,plain,(
    r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f20,plain,(
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
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f22,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f23,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f24,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f26,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f19,plain,(
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
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,
    ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_383,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_526,plain,
    ( k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != X0_48
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != X0_48
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_536,plain,
    ( k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_382,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_522,plain,
    ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_5,negated_conjecture,
    ( r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_237,plain,
    ( ~ v1_xboole_0(X0)
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != X1
    | u1_struct_0(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_5])).

cnf(c_238,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_298,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_238])).

cnf(c_299,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | m1_subset_1(k7_domain_1(u1_struct_0(sK1),X0,X1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
    | m1_subset_1(k7_domain_1(u1_struct_0(sK1),X0_46,X1_46),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_299])).

cnf(c_518,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_519,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_1,plain,
    ( ~ v4_yellow_0(X0,X1)
    | ~ m1_yellow_0(X0,X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,negated_conjecture,
    ( m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_203,plain,
    ( ~ v4_yellow_0(X0,X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_yellow_0(X1,X2) = k1_yellow_0(X0,X2)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_204,plain,
    ( ~ v4_yellow_0(sK1,sK0)
    | ~ r1_yellow_0(sK0,X0)
    | ~ r2_hidden(k1_yellow_0(sK0,X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_14,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_13,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_12,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_11,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_10,negated_conjecture,
    ( v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_208,plain,
    ( ~ r1_yellow_0(sK0,X0)
    | ~ r2_hidden(k1_yellow_0(sK0,X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_204,c_14,c_13,c_12,c_11,c_10])).

cnf(c_244,plain,
    ( ~ r1_yellow_0(sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK0,X0)
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK0,X0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_5,c_208])).

cnf(c_329,plain,
    ( ~ r1_yellow_0(sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK0,X0)
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK0,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_244])).

cnf(c_375,plain,
    ( ~ r1_yellow_0(sK0,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_yellow_0(sK1,X0_46) = k1_yellow_0(sK0,X0_46)
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK0,X0_46) ),
    inference(subtyping,[status(esa)],[c_329])).

cnf(c_511,plain,
    ( ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_512,plain,
    ( k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != iProver_top
    | m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_2,plain,
    ( ~ v4_yellow_0(X0,X1)
    | ~ m1_yellow_0(X0,X1)
    | ~ r1_yellow_0(X1,X2)
    | r1_yellow_0(X0,X2)
    | ~ r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_179,plain,
    ( ~ v4_yellow_0(X0,X1)
    | ~ r1_yellow_0(X1,X2)
    | r1_yellow_0(X0,X2)
    | ~ r2_hidden(k1_yellow_0(X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_180,plain,
    ( ~ v4_yellow_0(sK1,sK0)
    | r1_yellow_0(sK1,X0)
    | ~ r1_yellow_0(sK0,X0)
    | ~ r2_hidden(k1_yellow_0(sK0,X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_179])).

cnf(c_184,plain,
    ( r1_yellow_0(sK1,X0)
    | ~ r1_yellow_0(sK0,X0)
    | ~ r2_hidden(k1_yellow_0(sK0,X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_180,c_14,c_13,c_12,c_11,c_10])).

cnf(c_264,plain,
    ( r1_yellow_0(sK1,X0)
    | ~ r1_yellow_0(sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK0,X0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_5,c_184])).

cnf(c_325,plain,
    ( r1_yellow_0(sK1,X0)
    | ~ r1_yellow_0(sK0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK0,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_264])).

cnf(c_376,plain,
    ( r1_yellow_0(sK1,X0_46)
    | ~ r1_yellow_0(sK0,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK0,X0_46) ),
    inference(subtyping,[status(esa)],[c_325])).

cnf(c_508,plain,
    ( r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_509,plain,
    ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = iProver_top
    | r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != iProver_top
    | m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_4,negated_conjecture,
    ( ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_381,negated_conjecture,
    ( ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_385,plain,
    ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_6,negated_conjecture,
    ( r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_23,plain,
    ( r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_536,c_522,c_519,c_512,c_509,c_385,c_23,c_22,c_21])).


%------------------------------------------------------------------------------
