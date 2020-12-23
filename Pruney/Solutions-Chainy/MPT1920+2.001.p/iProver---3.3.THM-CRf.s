%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:04 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  171 (1144 expanded)
%              Number of clauses        :  119 ( 326 expanded)
%              Number of leaves         :   14 ( 394 expanded)
%              Depth                    :   21
%              Number of atoms          :  544 (5120 expanded)
%              Number of equality atoms :  147 ( 303 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_yellow_6(X3,X0,X2)
                 => m1_yellow_6(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_6(X2,X0,X1)
               => ! [X3] :
                    ( m1_yellow_6(X3,X0,X2)
                   => m1_yellow_6(X3,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_yellow_6(X3,X0,X1)
                  & m1_yellow_6(X3,X0,X2) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_yellow_6(X3,X0,X1)
          & m1_yellow_6(X3,X0,X2) )
     => ( ~ m1_yellow_6(sK3,X0,X1)
        & m1_yellow_6(sK3,X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_yellow_6(X3,X0,X1)
              & m1_yellow_6(X3,X0,X2) )
          & m1_yellow_6(X2,X0,X1) )
     => ( ? [X3] :
            ( ~ m1_yellow_6(X3,X0,X1)
            & m1_yellow_6(X3,X0,sK2) )
        & m1_yellow_6(sK2,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_yellow_6(X3,X0,X1)
                  & m1_yellow_6(X3,X0,X2) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_yellow_6(X3,X0,sK1)
                & m1_yellow_6(X3,X0,X2) )
            & m1_yellow_6(X2,X0,sK1) )
        & l1_waybel_0(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_yellow_6(X3,X0,X1)
                    & m1_yellow_6(X3,X0,X2) )
                & m1_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_yellow_6(X3,sK0,X1)
                  & m1_yellow_6(X3,sK0,X2) )
              & m1_yellow_6(X2,sK0,X1) )
          & l1_waybel_0(X1,sK0) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ m1_yellow_6(sK3,sK0,sK1)
    & m1_yellow_6(sK3,sK0,sK2)
    & m1_yellow_6(sK2,sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f34,f33,f32,f31])).

fof(f53,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    m1_yellow_6(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) = u1_waybel_0(X0,X2)
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) = u1_waybel_0(X0,X2)
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) != u1_waybel_0(X0,X2)
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) = u1_waybel_0(X0,X2)
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) != u1_waybel_0(X0,X2)
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) = u1_waybel_0(X0,X2)
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) = u1_waybel_0(X0,X2)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
          & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
        & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) )
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
        & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) )
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ~ m1_yellow_6(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_6(X2,X0,X1)
      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) != u1_waybel_0(X0,X2)
      | ~ m1_yellow_0(X2,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_0(X2,X1)
             => m1_yellow_0(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_yellow_0(X2,X0)
              | ~ m1_yellow_0(X2,X1) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X0)
      | ~ m1_yellow_0(X2,X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_17,negated_conjecture,
    ( m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_420,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_421,plain,
    ( ~ m1_yellow_6(X0,sK0,X1)
    | ~ l1_waybel_0(X1,sK0)
    | l1_waybel_0(X0,sK0) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_773,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | l1_waybel_0(X1,sK0)
    | sK2 != X1
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_421])).

cnf(c_774,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ l1_waybel_0(sK1,sK0) ),
    inference(unflattening,[status(thm)],[c_773])).

cnf(c_18,negated_conjecture,
    ( l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_776,plain,
    ( l1_waybel_0(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_774,c_18])).

cnf(c_16,negated_conjecture,
    ( m1_yellow_6(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) = u1_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_117,plain,
    ( ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_struct_0(X1)
    | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) = u1_waybel_0(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_13])).

cnf(c_118,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) = u1_waybel_0(X1,X0) ),
    inference(renaming,[status(thm)],[c_117])).

cnf(c_390,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) = u1_waybel_0(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_118,c_19])).

cnf(c_391,plain,
    ( ~ m1_yellow_6(X0,sK0,X1)
    | ~ l1_waybel_0(X1,sK0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1),u1_struct_0(X0)) = u1_waybel_0(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_763,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0),u1_struct_0(X1)) = u1_waybel_0(sK0,X1)
    | sK2 != X0
    | sK0 != sK0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_391])).

cnf(c_764,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) = u1_waybel_0(sK0,sK3) ),
    inference(unflattening,[status(thm)],[c_763])).

cnf(c_783,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) = u1_waybel_0(sK0,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_776,c_764])).

cnf(c_1326,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) = u1_waybel_0(sK0,sK3) ),
    inference(subtyping,[status(esa)],[c_783])).

cnf(c_8,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_466,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_467,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_985,plain,
    ( m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_467,c_776])).

cnf(c_986,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_985])).

cnf(c_1307,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_986])).

cnf(c_1805,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1307])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | v1_funct_1(u1_waybel_0(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_454,plain,
    ( ~ l1_waybel_0(X0,X1)
    | v1_funct_1(u1_waybel_0(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_455,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | v1_funct_1(u1_waybel_0(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_559,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | u1_waybel_0(sK0,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_455])).

cnf(c_560,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,u1_waybel_0(sK0,X0),X3) = k7_relat_1(u1_waybel_0(sK0,X0),X3) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_966,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,u1_waybel_0(sK0,X0),X3) = k7_relat_1(u1_waybel_0(sK0,X0),X3)
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_560,c_776])).

cnf(c_967,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,u1_waybel_0(sK0,sK2),X2) = k7_relat_1(u1_waybel_0(sK0,sK2),X2) ),
    inference(unflattening,[status(thm)],[c_966])).

cnf(c_1309,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_partfun1(X0_52,X1_52,u1_waybel_0(sK0,sK2),X2_52) = k7_relat_1(u1_waybel_0(sK0,sK2),X2_52) ),
    inference(subtyping,[status(esa)],[c_967])).

cnf(c_1803,plain,
    ( k2_partfun1(X0_52,X1_52,u1_waybel_0(sK0,sK2),X2_52) = k7_relat_1(u1_waybel_0(sK0,sK2),X2_52)
    | m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1309])).

cnf(c_2662,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2),X0_52) = k7_relat_1(u1_waybel_0(sK0,sK2),X0_52) ),
    inference(superposition,[status(thm)],[c_1805,c_1803])).

cnf(c_3208,plain,
    ( k7_relat_1(u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) = u1_waybel_0(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_1326,c_2662])).

cnf(c_12,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X0,X1)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_112,plain,
    ( ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_6(X0,X1,X2)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_13])).

cnf(c_113,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_112])).

cnf(c_405,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_113,c_19])).

cnf(c_406,plain,
    ( ~ m1_yellow_6(X0,sK0,X1)
    | ~ l1_waybel_0(X1,sK0)
    | m1_yellow_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_753,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | m1_yellow_0(X1,X0)
    | sK2 != X0
    | sK0 != sK0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_406])).

cnf(c_754,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | m1_yellow_0(sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_785,plain,
    ( m1_yellow_0(sK3,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_776,c_754])).

cnf(c_1325,plain,
    ( m1_yellow_0(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_785])).

cnf(c_1788,plain,
    ( m1_yellow_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1325])).

cnf(c_6,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1330,plain,
    ( ~ m1_yellow_0(X0_50,X1_50)
    | r1_tarski(u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ l1_orders_2(X1_50)
    | ~ l1_orders_2(X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1786,plain,
    ( m1_yellow_0(X0_50,X1_50) != iProver_top
    | r1_tarski(u1_struct_0(X0_50),u1_struct_0(X1_50)) = iProver_top
    | l1_orders_2(X1_50) != iProver_top
    | l1_orders_2(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_592,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | u1_waybel_0(sK0,X0) != X3
    | k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ),
    inference(resolution_lifted,[status(thm)],[c_0,c_455])).

cnf(c_593,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(u1_waybel_0(sK0,X0))
    | k7_relat_1(k7_relat_1(u1_waybel_0(sK0,X0),X2),X1) = k7_relat_1(u1_waybel_0(sK0,X0),X1) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_830,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(u1_waybel_0(sK0,X2))
    | k7_relat_1(k7_relat_1(u1_waybel_0(sK0,X2),X1),X0) = k7_relat_1(u1_waybel_0(sK0,X2),X0)
    | sK1 != X2
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_593])).

cnf(c_831,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(u1_waybel_0(sK0,sK1))
    | k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),X1),X0) = k7_relat_1(u1_waybel_0(sK0,sK1),X0) ),
    inference(unflattening,[status(thm)],[c_830])).

cnf(c_1321,plain,
    ( ~ r1_tarski(X0_52,X1_52)
    | ~ v1_relat_1(u1_waybel_0(sK0,sK1))
    | k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),X1_52),X0_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X0_52) ),
    inference(subtyping,[status(esa)],[c_831])).

cnf(c_1791,plain,
    ( k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),X0_52),X1_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X1_52)
    | r1_tarski(X1_52,X0_52) != iProver_top
    | v1_relat_1(u1_waybel_0(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_877,plain,
    ( m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_467])).

cnf(c_878,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_877])).

cnf(c_879,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_878])).

cnf(c_1380,plain,
    ( k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),X0_52),X1_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X1_52)
    | r1_tarski(X1_52,X0_52) != iProver_top
    | v1_relat_1(u1_waybel_0(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1333,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1976,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_relat_1(u1_waybel_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_1977,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_relat_1(u1_waybel_0(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1976])).

cnf(c_2249,plain,
    ( r1_tarski(X1_52,X0_52) != iProver_top
    | k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),X0_52),X1_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X1_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1791,c_879,c_1380,c_1977])).

cnf(c_2250,plain,
    ( k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),X0_52),X1_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X1_52)
    | r1_tarski(X1_52,X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_2249])).

cnf(c_2257,plain,
    ( k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(X0_50)),u1_struct_0(X1_50)) = k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(X1_50))
    | m1_yellow_0(X1_50,X0_50) != iProver_top
    | l1_orders_2(X0_50) != iProver_top
    | l1_orders_2(X1_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_2250])).

cnf(c_2808,plain,
    ( k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK2)),u1_struct_0(sK3)) = k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3))
    | l1_orders_2(sK2) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1788,c_2257])).

cnf(c_800,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0),u1_struct_0(X1)) = u1_waybel_0(sK0,X1)
    | sK2 != X1
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_391])).

cnf(c_801,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK2)) = u1_waybel_0(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_800])).

cnf(c_803,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK2)) = u1_waybel_0(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_801,c_18])).

cnf(c_1323,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK2)) = u1_waybel_0(sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_803])).

cnf(c_1317,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_878])).

cnf(c_1795,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1317])).

cnf(c_858,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,u1_waybel_0(sK0,X0),X3) = k7_relat_1(u1_waybel_0(sK0,X0),X3)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_560])).

cnf(c_859,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,u1_waybel_0(sK0,sK1),X2) = k7_relat_1(u1_waybel_0(sK0,sK1),X2) ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_1319,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_partfun1(X0_52,X1_52,u1_waybel_0(sK0,sK1),X2_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X2_52) ),
    inference(subtyping,[status(esa)],[c_859])).

cnf(c_1793,plain,
    ( k2_partfun1(X0_52,X1_52,u1_waybel_0(sK0,sK1),X2_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X2_52)
    | m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_2083,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X0_52) ),
    inference(superposition,[status(thm)],[c_1795,c_1793])).

cnf(c_2535,plain,
    ( k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK2)) = u1_waybel_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_1323,c_2083])).

cnf(c_2820,plain,
    ( k7_relat_1(u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) = k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3))
    | l1_orders_2(sK2) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2808,c_2535])).

cnf(c_7,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_478,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_479,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_743,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | l1_waybel_0(X1,sK0)
    | sK2 != X0
    | sK0 != sK0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_421])).

cnf(c_744,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | l1_waybel_0(sK3,sK0) ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_784,plain,
    ( l1_waybel_0(sK3,sK0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_776,c_744])).

cnf(c_924,plain,
    ( l1_orders_2(X0)
    | sK0 != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_479,c_784])).

cnf(c_925,plain,
    ( l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_924])).

cnf(c_926,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_978,plain,
    ( l1_orders_2(X0)
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_479,c_776])).

cnf(c_979,plain,
    ( l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_978])).

cnf(c_980,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_979])).

cnf(c_2886,plain,
    ( k7_relat_1(u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) = k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2820,c_926,c_980])).

cnf(c_3211,plain,
    ( k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) = u1_waybel_0(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_3208,c_2886])).

cnf(c_15,negated_conjecture,
    ( ~ m1_yellow_6(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_10,plain,
    ( m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1)
    | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) != u1_waybel_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_433,plain,
    ( m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_yellow_0(X0,X2)
    | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) != u1_waybel_0(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_434,plain,
    ( m1_yellow_6(X0,sK0,X1)
    | ~ l1_waybel_0(X1,sK0)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_yellow_0(X0,X1)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1),u1_struct_0(X0)) != u1_waybel_0(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_726,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | ~ l1_waybel_0(X1,sK0)
    | ~ m1_yellow_0(X1,X0)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0),u1_struct_0(X1)) != u1_waybel_0(sK0,X1)
    | sK1 != X0
    | sK0 != sK0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_434])).

cnf(c_727,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK3,sK0)
    | ~ m1_yellow_0(sK3,sK1)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_729,plain,
    ( ~ l1_waybel_0(sK3,sK0)
    | ~ m1_yellow_0(sK3,sK1)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_18])).

cnf(c_822,plain,
    ( ~ m1_yellow_0(sK3,sK1)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_784,c_729])).

cnf(c_1322,plain,
    ( ~ m1_yellow_0(sK3,sK1)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3) ),
    inference(subtyping,[status(esa)],[c_822])).

cnf(c_1790,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3)
    | m1_yellow_0(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_789,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | m1_yellow_0(X1,X0)
    | sK2 != X1
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_406])).

cnf(c_790,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | m1_yellow_0(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_870,plain,
    ( l1_orders_2(X0)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_479])).

cnf(c_871,plain,
    ( l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_870])).

cnf(c_14,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ m1_yellow_0(X2,X0)
    | m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1329,plain,
    ( ~ m1_yellow_0(X0_50,X1_50)
    | ~ m1_yellow_0(X2_50,X0_50)
    | m1_yellow_0(X2_50,X1_50)
    | ~ l1_orders_2(X1_50) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2055,plain,
    ( ~ m1_yellow_0(X0_50,X1_50)
    | ~ m1_yellow_0(X1_50,sK1)
    | m1_yellow_0(X0_50,sK1)
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_1329])).

cnf(c_2368,plain,
    ( ~ m1_yellow_0(X0_50,sK2)
    | m1_yellow_0(X0_50,sK1)
    | ~ m1_yellow_0(sK2,sK1)
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_2055])).

cnf(c_2531,plain,
    ( ~ m1_yellow_0(sK2,sK1)
    | ~ m1_yellow_0(sK3,sK2)
    | m1_yellow_0(sK3,sK1)
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_2538,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1790,c_18,c_754,c_774,c_790,c_871,c_1322,c_2531])).

cnf(c_2540,plain,
    ( k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_2538,c_2083])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3211,c_2540])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.95/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.00  
% 1.95/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.95/1.00  
% 1.95/1.00  ------  iProver source info
% 1.95/1.00  
% 1.95/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.95/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.95/1.00  git: non_committed_changes: false
% 1.95/1.00  git: last_make_outside_of_git: false
% 1.95/1.00  
% 1.95/1.00  ------ 
% 1.95/1.00  
% 1.95/1.00  ------ Input Options
% 1.95/1.00  
% 1.95/1.00  --out_options                           all
% 1.95/1.00  --tptp_safe_out                         true
% 1.95/1.00  --problem_path                          ""
% 1.95/1.00  --include_path                          ""
% 1.95/1.00  --clausifier                            res/vclausify_rel
% 1.95/1.00  --clausifier_options                    --mode clausify
% 1.95/1.00  --stdin                                 false
% 1.95/1.00  --stats_out                             all
% 1.95/1.00  
% 1.95/1.00  ------ General Options
% 1.95/1.00  
% 1.95/1.00  --fof                                   false
% 1.95/1.00  --time_out_real                         305.
% 1.95/1.00  --time_out_virtual                      -1.
% 1.95/1.00  --symbol_type_check                     false
% 1.95/1.00  --clausify_out                          false
% 1.95/1.00  --sig_cnt_out                           false
% 1.95/1.00  --trig_cnt_out                          false
% 1.95/1.00  --trig_cnt_out_tolerance                1.
% 1.95/1.00  --trig_cnt_out_sk_spl                   false
% 1.95/1.00  --abstr_cl_out                          false
% 1.95/1.00  
% 1.95/1.00  ------ Global Options
% 1.95/1.00  
% 1.95/1.00  --schedule                              default
% 1.95/1.00  --add_important_lit                     false
% 1.95/1.00  --prop_solver_per_cl                    1000
% 1.95/1.00  --min_unsat_core                        false
% 1.95/1.00  --soft_assumptions                      false
% 1.95/1.00  --soft_lemma_size                       3
% 1.95/1.00  --prop_impl_unit_size                   0
% 1.95/1.00  --prop_impl_unit                        []
% 1.95/1.00  --share_sel_clauses                     true
% 1.95/1.00  --reset_solvers                         false
% 1.95/1.00  --bc_imp_inh                            [conj_cone]
% 1.95/1.00  --conj_cone_tolerance                   3.
% 1.95/1.00  --extra_neg_conj                        none
% 1.95/1.00  --large_theory_mode                     true
% 1.95/1.00  --prolific_symb_bound                   200
% 1.95/1.00  --lt_threshold                          2000
% 1.95/1.00  --clause_weak_htbl                      true
% 1.95/1.00  --gc_record_bc_elim                     false
% 1.95/1.00  
% 1.95/1.00  ------ Preprocessing Options
% 1.95/1.00  
% 1.95/1.00  --preprocessing_flag                    true
% 1.95/1.00  --time_out_prep_mult                    0.1
% 1.95/1.00  --splitting_mode                        input
% 1.95/1.00  --splitting_grd                         true
% 1.95/1.00  --splitting_cvd                         false
% 1.95/1.00  --splitting_cvd_svl                     false
% 1.95/1.00  --splitting_nvd                         32
% 1.95/1.00  --sub_typing                            true
% 1.95/1.00  --prep_gs_sim                           true
% 1.95/1.00  --prep_unflatten                        true
% 1.95/1.00  --prep_res_sim                          true
% 1.95/1.00  --prep_upred                            true
% 1.95/1.00  --prep_sem_filter                       exhaustive
% 1.95/1.00  --prep_sem_filter_out                   false
% 1.95/1.00  --pred_elim                             true
% 1.95/1.00  --res_sim_input                         true
% 1.95/1.00  --eq_ax_congr_red                       true
% 1.95/1.00  --pure_diseq_elim                       true
% 1.95/1.00  --brand_transform                       false
% 1.95/1.00  --non_eq_to_eq                          false
% 1.95/1.00  --prep_def_merge                        true
% 1.95/1.00  --prep_def_merge_prop_impl              false
% 1.95/1.00  --prep_def_merge_mbd                    true
% 1.95/1.00  --prep_def_merge_tr_red                 false
% 1.95/1.00  --prep_def_merge_tr_cl                  false
% 1.95/1.00  --smt_preprocessing                     true
% 1.95/1.00  --smt_ac_axioms                         fast
% 1.95/1.00  --preprocessed_out                      false
% 1.95/1.00  --preprocessed_stats                    false
% 1.95/1.00  
% 1.95/1.00  ------ Abstraction refinement Options
% 1.95/1.00  
% 1.95/1.00  --abstr_ref                             []
% 1.95/1.00  --abstr_ref_prep                        false
% 1.95/1.00  --abstr_ref_until_sat                   false
% 1.95/1.00  --abstr_ref_sig_restrict                funpre
% 1.95/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.95/1.00  --abstr_ref_under                       []
% 1.95/1.00  
% 1.95/1.00  ------ SAT Options
% 1.95/1.00  
% 1.95/1.00  --sat_mode                              false
% 1.95/1.00  --sat_fm_restart_options                ""
% 1.95/1.00  --sat_gr_def                            false
% 1.95/1.00  --sat_epr_types                         true
% 1.95/1.00  --sat_non_cyclic_types                  false
% 1.95/1.00  --sat_finite_models                     false
% 1.95/1.00  --sat_fm_lemmas                         false
% 1.95/1.00  --sat_fm_prep                           false
% 1.95/1.00  --sat_fm_uc_incr                        true
% 1.95/1.00  --sat_out_model                         small
% 1.95/1.00  --sat_out_clauses                       false
% 1.95/1.00  
% 1.95/1.00  ------ QBF Options
% 1.95/1.00  
% 1.95/1.00  --qbf_mode                              false
% 1.95/1.00  --qbf_elim_univ                         false
% 1.95/1.00  --qbf_dom_inst                          none
% 1.95/1.00  --qbf_dom_pre_inst                      false
% 1.95/1.00  --qbf_sk_in                             false
% 1.95/1.00  --qbf_pred_elim                         true
% 1.95/1.00  --qbf_split                             512
% 1.95/1.00  
% 1.95/1.00  ------ BMC1 Options
% 1.95/1.00  
% 1.95/1.00  --bmc1_incremental                      false
% 1.95/1.00  --bmc1_axioms                           reachable_all
% 1.95/1.00  --bmc1_min_bound                        0
% 1.95/1.00  --bmc1_max_bound                        -1
% 1.95/1.00  --bmc1_max_bound_default                -1
% 1.95/1.00  --bmc1_symbol_reachability              true
% 1.95/1.00  --bmc1_property_lemmas                  false
% 1.95/1.00  --bmc1_k_induction                      false
% 1.95/1.00  --bmc1_non_equiv_states                 false
% 1.95/1.00  --bmc1_deadlock                         false
% 1.95/1.00  --bmc1_ucm                              false
% 1.95/1.00  --bmc1_add_unsat_core                   none
% 1.95/1.00  --bmc1_unsat_core_children              false
% 1.95/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.95/1.00  --bmc1_out_stat                         full
% 1.95/1.00  --bmc1_ground_init                      false
% 1.95/1.00  --bmc1_pre_inst_next_state              false
% 1.95/1.00  --bmc1_pre_inst_state                   false
% 1.95/1.00  --bmc1_pre_inst_reach_state             false
% 1.95/1.00  --bmc1_out_unsat_core                   false
% 1.95/1.00  --bmc1_aig_witness_out                  false
% 1.95/1.00  --bmc1_verbose                          false
% 1.95/1.00  --bmc1_dump_clauses_tptp                false
% 1.95/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.95/1.00  --bmc1_dump_file                        -
% 1.95/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.95/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.95/1.00  --bmc1_ucm_extend_mode                  1
% 1.95/1.00  --bmc1_ucm_init_mode                    2
% 1.95/1.00  --bmc1_ucm_cone_mode                    none
% 1.95/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.95/1.00  --bmc1_ucm_relax_model                  4
% 1.95/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.95/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.95/1.00  --bmc1_ucm_layered_model                none
% 1.95/1.00  --bmc1_ucm_max_lemma_size               10
% 1.95/1.00  
% 1.95/1.00  ------ AIG Options
% 1.95/1.00  
% 1.95/1.00  --aig_mode                              false
% 1.95/1.00  
% 1.95/1.00  ------ Instantiation Options
% 1.95/1.00  
% 1.95/1.00  --instantiation_flag                    true
% 1.95/1.00  --inst_sos_flag                         false
% 1.95/1.00  --inst_sos_phase                        true
% 1.95/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.95/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.95/1.00  --inst_lit_sel_side                     num_symb
% 1.95/1.00  --inst_solver_per_active                1400
% 1.95/1.00  --inst_solver_calls_frac                1.
% 1.95/1.00  --inst_passive_queue_type               priority_queues
% 1.95/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.95/1.00  --inst_passive_queues_freq              [25;2]
% 1.95/1.00  --inst_dismatching                      true
% 1.95/1.00  --inst_eager_unprocessed_to_passive     true
% 1.95/1.00  --inst_prop_sim_given                   true
% 1.95/1.00  --inst_prop_sim_new                     false
% 1.95/1.00  --inst_subs_new                         false
% 1.95/1.00  --inst_eq_res_simp                      false
% 1.95/1.00  --inst_subs_given                       false
% 1.95/1.00  --inst_orphan_elimination               true
% 1.95/1.00  --inst_learning_loop_flag               true
% 1.95/1.00  --inst_learning_start                   3000
% 1.95/1.00  --inst_learning_factor                  2
% 1.95/1.00  --inst_start_prop_sim_after_learn       3
% 1.95/1.00  --inst_sel_renew                        solver
% 1.95/1.00  --inst_lit_activity_flag                true
% 1.95/1.00  --inst_restr_to_given                   false
% 1.95/1.00  --inst_activity_threshold               500
% 1.95/1.00  --inst_out_proof                        true
% 1.95/1.00  
% 1.95/1.00  ------ Resolution Options
% 1.95/1.00  
% 1.95/1.00  --resolution_flag                       true
% 1.95/1.00  --res_lit_sel                           adaptive
% 1.95/1.00  --res_lit_sel_side                      none
% 1.95/1.00  --res_ordering                          kbo
% 1.95/1.00  --res_to_prop_solver                    active
% 1.95/1.00  --res_prop_simpl_new                    false
% 1.95/1.00  --res_prop_simpl_given                  true
% 1.95/1.00  --res_passive_queue_type                priority_queues
% 1.95/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.95/1.00  --res_passive_queues_freq               [15;5]
% 1.95/1.00  --res_forward_subs                      full
% 1.95/1.00  --res_backward_subs                     full
% 1.95/1.00  --res_forward_subs_resolution           true
% 1.95/1.00  --res_backward_subs_resolution          true
% 1.95/1.00  --res_orphan_elimination                true
% 1.95/1.00  --res_time_limit                        2.
% 1.95/1.00  --res_out_proof                         true
% 1.95/1.00  
% 1.95/1.00  ------ Superposition Options
% 1.95/1.00  
% 1.95/1.00  --superposition_flag                    true
% 1.95/1.00  --sup_passive_queue_type                priority_queues
% 1.95/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.95/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.95/1.00  --demod_completeness_check              fast
% 1.95/1.00  --demod_use_ground                      true
% 1.95/1.00  --sup_to_prop_solver                    passive
% 1.95/1.00  --sup_prop_simpl_new                    true
% 1.95/1.00  --sup_prop_simpl_given                  true
% 1.95/1.00  --sup_fun_splitting                     false
% 1.95/1.00  --sup_smt_interval                      50000
% 1.95/1.00  
% 1.95/1.00  ------ Superposition Simplification Setup
% 1.95/1.00  
% 1.95/1.00  --sup_indices_passive                   []
% 1.95/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.95/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.00  --sup_full_bw                           [BwDemod]
% 1.95/1.00  --sup_immed_triv                        [TrivRules]
% 1.95/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.95/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.00  --sup_immed_bw_main                     []
% 1.95/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.95/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/1.00  
% 1.95/1.00  ------ Combination Options
% 1.95/1.00  
% 1.95/1.00  --comb_res_mult                         3
% 1.95/1.00  --comb_sup_mult                         2
% 1.95/1.00  --comb_inst_mult                        10
% 1.95/1.00  
% 1.95/1.00  ------ Debug Options
% 1.95/1.00  
% 1.95/1.00  --dbg_backtrace                         false
% 1.95/1.00  --dbg_dump_prop_clauses                 false
% 1.95/1.00  --dbg_dump_prop_clauses_file            -
% 1.95/1.00  --dbg_out_stat                          false
% 1.95/1.00  ------ Parsing...
% 1.95/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.95/1.00  
% 1.95/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 1.95/1.00  
% 1.95/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.95/1.00  
% 1.95/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.95/1.00  ------ Proving...
% 1.95/1.00  ------ Problem Properties 
% 1.95/1.00  
% 1.95/1.00  
% 1.95/1.00  clauses                                 27
% 1.95/1.00  conjectures                             0
% 1.95/1.00  EPR                                     8
% 1.95/1.00  Horn                                    27
% 1.95/1.00  unary                                   10
% 1.95/1.00  binary                                  5
% 1.95/1.00  lits                                    61
% 1.95/1.00  lits eq                                 18
% 1.95/1.00  fd_pure                                 0
% 1.95/1.00  fd_pseudo                               0
% 1.95/1.00  fd_cond                                 0
% 1.95/1.00  fd_pseudo_cond                          0
% 1.95/1.00  AC symbols                              0
% 1.95/1.00  
% 1.95/1.00  ------ Schedule dynamic 5 is on 
% 1.95/1.00  
% 1.95/1.00  ------ no conjectures: strip conj schedule 
% 1.95/1.00  
% 1.95/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.95/1.00  
% 1.95/1.00  
% 1.95/1.00  ------ 
% 1.95/1.00  Current options:
% 1.95/1.00  ------ 
% 1.95/1.00  
% 1.95/1.00  ------ Input Options
% 1.95/1.00  
% 1.95/1.00  --out_options                           all
% 1.95/1.00  --tptp_safe_out                         true
% 1.95/1.00  --problem_path                          ""
% 1.95/1.00  --include_path                          ""
% 1.95/1.00  --clausifier                            res/vclausify_rel
% 1.95/1.00  --clausifier_options                    --mode clausify
% 1.95/1.00  --stdin                                 false
% 1.95/1.00  --stats_out                             all
% 1.95/1.00  
% 1.95/1.00  ------ General Options
% 1.95/1.00  
% 1.95/1.00  --fof                                   false
% 1.95/1.00  --time_out_real                         305.
% 1.95/1.00  --time_out_virtual                      -1.
% 1.95/1.00  --symbol_type_check                     false
% 1.95/1.00  --clausify_out                          false
% 1.95/1.00  --sig_cnt_out                           false
% 1.95/1.00  --trig_cnt_out                          false
% 1.95/1.00  --trig_cnt_out_tolerance                1.
% 1.95/1.00  --trig_cnt_out_sk_spl                   false
% 1.95/1.00  --abstr_cl_out                          false
% 1.95/1.00  
% 1.95/1.00  ------ Global Options
% 1.95/1.00  
% 1.95/1.00  --schedule                              default
% 1.95/1.00  --add_important_lit                     false
% 1.95/1.00  --prop_solver_per_cl                    1000
% 1.95/1.00  --min_unsat_core                        false
% 1.95/1.00  --soft_assumptions                      false
% 1.95/1.00  --soft_lemma_size                       3
% 1.95/1.00  --prop_impl_unit_size                   0
% 1.95/1.00  --prop_impl_unit                        []
% 1.95/1.00  --share_sel_clauses                     true
% 1.95/1.00  --reset_solvers                         false
% 1.95/1.00  --bc_imp_inh                            [conj_cone]
% 1.95/1.00  --conj_cone_tolerance                   3.
% 1.95/1.00  --extra_neg_conj                        none
% 1.95/1.00  --large_theory_mode                     true
% 1.95/1.00  --prolific_symb_bound                   200
% 1.95/1.00  --lt_threshold                          2000
% 1.95/1.00  --clause_weak_htbl                      true
% 1.95/1.00  --gc_record_bc_elim                     false
% 1.95/1.00  
% 1.95/1.00  ------ Preprocessing Options
% 1.95/1.00  
% 1.95/1.00  --preprocessing_flag                    true
% 1.95/1.00  --time_out_prep_mult                    0.1
% 1.95/1.00  --splitting_mode                        input
% 1.95/1.00  --splitting_grd                         true
% 1.95/1.00  --splitting_cvd                         false
% 1.95/1.00  --splitting_cvd_svl                     false
% 1.95/1.00  --splitting_nvd                         32
% 1.95/1.00  --sub_typing                            true
% 1.95/1.00  --prep_gs_sim                           true
% 1.95/1.00  --prep_unflatten                        true
% 1.95/1.00  --prep_res_sim                          true
% 1.95/1.00  --prep_upred                            true
% 1.95/1.00  --prep_sem_filter                       exhaustive
% 1.95/1.00  --prep_sem_filter_out                   false
% 1.95/1.00  --pred_elim                             true
% 1.95/1.00  --res_sim_input                         true
% 1.95/1.00  --eq_ax_congr_red                       true
% 1.95/1.00  --pure_diseq_elim                       true
% 1.95/1.00  --brand_transform                       false
% 1.95/1.00  --non_eq_to_eq                          false
% 1.95/1.00  --prep_def_merge                        true
% 1.95/1.00  --prep_def_merge_prop_impl              false
% 1.95/1.00  --prep_def_merge_mbd                    true
% 1.95/1.00  --prep_def_merge_tr_red                 false
% 1.95/1.00  --prep_def_merge_tr_cl                  false
% 1.95/1.00  --smt_preprocessing                     true
% 1.95/1.00  --smt_ac_axioms                         fast
% 1.95/1.00  --preprocessed_out                      false
% 1.95/1.00  --preprocessed_stats                    false
% 1.95/1.00  
% 1.95/1.00  ------ Abstraction refinement Options
% 1.95/1.00  
% 1.95/1.00  --abstr_ref                             []
% 1.95/1.00  --abstr_ref_prep                        false
% 1.95/1.00  --abstr_ref_until_sat                   false
% 1.95/1.00  --abstr_ref_sig_restrict                funpre
% 1.95/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.95/1.00  --abstr_ref_under                       []
% 1.95/1.00  
% 1.95/1.00  ------ SAT Options
% 1.95/1.00  
% 1.95/1.00  --sat_mode                              false
% 1.95/1.00  --sat_fm_restart_options                ""
% 1.95/1.00  --sat_gr_def                            false
% 1.95/1.00  --sat_epr_types                         true
% 1.95/1.00  --sat_non_cyclic_types                  false
% 1.95/1.00  --sat_finite_models                     false
% 1.95/1.00  --sat_fm_lemmas                         false
% 1.95/1.00  --sat_fm_prep                           false
% 1.95/1.00  --sat_fm_uc_incr                        true
% 1.95/1.00  --sat_out_model                         small
% 1.95/1.00  --sat_out_clauses                       false
% 1.95/1.00  
% 1.95/1.00  ------ QBF Options
% 1.95/1.00  
% 1.95/1.00  --qbf_mode                              false
% 1.95/1.00  --qbf_elim_univ                         false
% 1.95/1.00  --qbf_dom_inst                          none
% 1.95/1.00  --qbf_dom_pre_inst                      false
% 1.95/1.00  --qbf_sk_in                             false
% 1.95/1.00  --qbf_pred_elim                         true
% 1.95/1.00  --qbf_split                             512
% 1.95/1.00  
% 1.95/1.00  ------ BMC1 Options
% 1.95/1.00  
% 1.95/1.00  --bmc1_incremental                      false
% 1.95/1.00  --bmc1_axioms                           reachable_all
% 1.95/1.00  --bmc1_min_bound                        0
% 1.95/1.00  --bmc1_max_bound                        -1
% 1.95/1.00  --bmc1_max_bound_default                -1
% 1.95/1.00  --bmc1_symbol_reachability              true
% 1.95/1.00  --bmc1_property_lemmas                  false
% 1.95/1.00  --bmc1_k_induction                      false
% 1.95/1.00  --bmc1_non_equiv_states                 false
% 1.95/1.00  --bmc1_deadlock                         false
% 1.95/1.00  --bmc1_ucm                              false
% 1.95/1.00  --bmc1_add_unsat_core                   none
% 1.95/1.00  --bmc1_unsat_core_children              false
% 1.95/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.95/1.00  --bmc1_out_stat                         full
% 1.95/1.00  --bmc1_ground_init                      false
% 1.95/1.00  --bmc1_pre_inst_next_state              false
% 1.95/1.00  --bmc1_pre_inst_state                   false
% 1.95/1.00  --bmc1_pre_inst_reach_state             false
% 1.95/1.00  --bmc1_out_unsat_core                   false
% 1.95/1.00  --bmc1_aig_witness_out                  false
% 1.95/1.00  --bmc1_verbose                          false
% 1.95/1.00  --bmc1_dump_clauses_tptp                false
% 1.95/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.95/1.00  --bmc1_dump_file                        -
% 1.95/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.95/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.95/1.00  --bmc1_ucm_extend_mode                  1
% 1.95/1.00  --bmc1_ucm_init_mode                    2
% 1.95/1.00  --bmc1_ucm_cone_mode                    none
% 1.95/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.95/1.00  --bmc1_ucm_relax_model                  4
% 1.95/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.95/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.95/1.00  --bmc1_ucm_layered_model                none
% 1.95/1.00  --bmc1_ucm_max_lemma_size               10
% 1.95/1.00  
% 1.95/1.00  ------ AIG Options
% 1.95/1.00  
% 1.95/1.00  --aig_mode                              false
% 1.95/1.00  
% 1.95/1.00  ------ Instantiation Options
% 1.95/1.00  
% 1.95/1.00  --instantiation_flag                    true
% 1.95/1.00  --inst_sos_flag                         false
% 1.95/1.00  --inst_sos_phase                        true
% 1.95/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.95/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.95/1.00  --inst_lit_sel_side                     none
% 1.95/1.00  --inst_solver_per_active                1400
% 1.95/1.00  --inst_solver_calls_frac                1.
% 1.95/1.00  --inst_passive_queue_type               priority_queues
% 1.95/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.95/1.00  --inst_passive_queues_freq              [25;2]
% 1.95/1.00  --inst_dismatching                      true
% 1.95/1.00  --inst_eager_unprocessed_to_passive     true
% 1.95/1.00  --inst_prop_sim_given                   true
% 1.95/1.00  --inst_prop_sim_new                     false
% 1.95/1.00  --inst_subs_new                         false
% 1.95/1.00  --inst_eq_res_simp                      false
% 1.95/1.00  --inst_subs_given                       false
% 1.95/1.00  --inst_orphan_elimination               true
% 1.95/1.00  --inst_learning_loop_flag               true
% 1.95/1.00  --inst_learning_start                   3000
% 1.95/1.00  --inst_learning_factor                  2
% 1.95/1.00  --inst_start_prop_sim_after_learn       3
% 1.95/1.00  --inst_sel_renew                        solver
% 1.95/1.00  --inst_lit_activity_flag                true
% 1.95/1.00  --inst_restr_to_given                   false
% 1.95/1.00  --inst_activity_threshold               500
% 1.95/1.00  --inst_out_proof                        true
% 1.95/1.00  
% 1.95/1.00  ------ Resolution Options
% 1.95/1.00  
% 1.95/1.00  --resolution_flag                       false
% 1.95/1.00  --res_lit_sel                           adaptive
% 1.95/1.00  --res_lit_sel_side                      none
% 1.95/1.00  --res_ordering                          kbo
% 1.95/1.00  --res_to_prop_solver                    active
% 1.95/1.00  --res_prop_simpl_new                    false
% 1.95/1.00  --res_prop_simpl_given                  true
% 1.95/1.00  --res_passive_queue_type                priority_queues
% 1.95/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.95/1.00  --res_passive_queues_freq               [15;5]
% 1.95/1.00  --res_forward_subs                      full
% 1.95/1.00  --res_backward_subs                     full
% 1.95/1.00  --res_forward_subs_resolution           true
% 1.95/1.00  --res_backward_subs_resolution          true
% 1.95/1.00  --res_orphan_elimination                true
% 1.95/1.00  --res_time_limit                        2.
% 1.95/1.00  --res_out_proof                         true
% 1.95/1.00  
% 1.95/1.00  ------ Superposition Options
% 1.95/1.00  
% 1.95/1.00  --superposition_flag                    true
% 1.95/1.00  --sup_passive_queue_type                priority_queues
% 1.95/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.95/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.95/1.00  --demod_completeness_check              fast
% 1.95/1.00  --demod_use_ground                      true
% 1.95/1.00  --sup_to_prop_solver                    passive
% 1.95/1.00  --sup_prop_simpl_new                    true
% 1.95/1.00  --sup_prop_simpl_given                  true
% 1.95/1.00  --sup_fun_splitting                     false
% 1.95/1.00  --sup_smt_interval                      50000
% 1.95/1.00  
% 1.95/1.00  ------ Superposition Simplification Setup
% 1.95/1.00  
% 1.95/1.00  --sup_indices_passive                   []
% 1.95/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.95/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.00  --sup_full_bw                           [BwDemod]
% 1.95/1.00  --sup_immed_triv                        [TrivRules]
% 1.95/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.95/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.00  --sup_immed_bw_main                     []
% 1.95/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.95/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/1.00  
% 1.95/1.00  ------ Combination Options
% 1.95/1.00  
% 1.95/1.00  --comb_res_mult                         3
% 1.95/1.00  --comb_sup_mult                         2
% 1.95/1.00  --comb_inst_mult                        10
% 1.95/1.00  
% 1.95/1.00  ------ Debug Options
% 1.95/1.00  
% 1.95/1.00  --dbg_backtrace                         false
% 1.95/1.00  --dbg_dump_prop_clauses                 false
% 1.95/1.00  --dbg_dump_prop_clauses_file            -
% 1.95/1.00  --dbg_out_stat                          false
% 1.95/1.00  
% 1.95/1.00  
% 1.95/1.00  
% 1.95/1.00  
% 1.95/1.00  ------ Proving...
% 1.95/1.00  
% 1.95/1.00  
% 1.95/1.00  % SZS status Theorem for theBenchmark.p
% 1.95/1.00  
% 1.95/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.95/1.00  
% 1.95/1.00  fof(f10,conjecture,(
% 1.95/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_yellow_6(X3,X0,X2) => m1_yellow_6(X3,X0,X1)))))),
% 1.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.00  
% 1.95/1.00  fof(f11,negated_conjecture,(
% 1.95/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_yellow_6(X3,X0,X2) => m1_yellow_6(X3,X0,X1)))))),
% 1.95/1.00    inference(negated_conjecture,[],[f10])).
% 1.95/1.00  
% 1.95/1.00  fof(f26,plain,(
% 1.95/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_yellow_6(X3,X0,X1) & m1_yellow_6(X3,X0,X2)) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 1.95/1.00    inference(ennf_transformation,[],[f11])).
% 1.95/1.00  
% 1.95/1.00  fof(f34,plain,(
% 1.95/1.00    ( ! [X2,X0,X1] : (? [X3] : (~m1_yellow_6(X3,X0,X1) & m1_yellow_6(X3,X0,X2)) => (~m1_yellow_6(sK3,X0,X1) & m1_yellow_6(sK3,X0,X2))) )),
% 1.95/1.00    introduced(choice_axiom,[])).
% 1.95/1.00  
% 1.95/1.00  fof(f33,plain,(
% 1.95/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_yellow_6(X3,X0,X1) & m1_yellow_6(X3,X0,X2)) & m1_yellow_6(X2,X0,X1)) => (? [X3] : (~m1_yellow_6(X3,X0,X1) & m1_yellow_6(X3,X0,sK2)) & m1_yellow_6(sK2,X0,X1))) )),
% 1.95/1.00    introduced(choice_axiom,[])).
% 1.95/1.00  
% 1.95/1.00  fof(f32,plain,(
% 1.95/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_yellow_6(X3,X0,X1) & m1_yellow_6(X3,X0,X2)) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) => (? [X2] : (? [X3] : (~m1_yellow_6(X3,X0,sK1) & m1_yellow_6(X3,X0,X2)) & m1_yellow_6(X2,X0,sK1)) & l1_waybel_0(sK1,X0))) )),
% 1.95/1.00    introduced(choice_axiom,[])).
% 1.95/1.00  
% 1.95/1.00  fof(f31,plain,(
% 1.95/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_yellow_6(X3,X0,X1) & m1_yellow_6(X3,X0,X2)) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_yellow_6(X3,sK0,X1) & m1_yellow_6(X3,sK0,X2)) & m1_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0)) & l1_struct_0(sK0))),
% 1.95/1.00    introduced(choice_axiom,[])).
% 1.95/1.00  
% 1.95/1.00  fof(f35,plain,(
% 1.95/1.00    (((~m1_yellow_6(sK3,sK0,sK1) & m1_yellow_6(sK3,sK0,sK2)) & m1_yellow_6(sK2,sK0,sK1)) & l1_waybel_0(sK1,sK0)) & l1_struct_0(sK0)),
% 1.95/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f34,f33,f32,f31])).
% 1.95/1.00  
% 1.95/1.00  fof(f53,plain,(
% 1.95/1.00    m1_yellow_6(sK2,sK0,sK1)),
% 1.95/1.00    inference(cnf_transformation,[],[f35])).
% 1.95/1.00  
% 1.95/1.00  fof(f8,axiom,(
% 1.95/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => ! [X2] : (m1_yellow_6(X2,X0,X1) => l1_waybel_0(X2,X0)))),
% 1.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.00  
% 1.95/1.00  fof(f23,plain,(
% 1.95/1.00    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 1.95/1.00    inference(ennf_transformation,[],[f8])).
% 1.95/1.00  
% 1.95/1.00  fof(f24,plain,(
% 1.95/1.00    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 1.95/1.00    inference(flattening,[],[f23])).
% 1.95/1.00  
% 1.95/1.00  fof(f49,plain,(
% 1.95/1.00    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.95/1.00    inference(cnf_transformation,[],[f24])).
% 1.95/1.00  
% 1.95/1.00  fof(f51,plain,(
% 1.95/1.00    l1_struct_0(sK0)),
% 1.95/1.00    inference(cnf_transformation,[],[f35])).
% 1.95/1.00  
% 1.95/1.00  fof(f52,plain,(
% 1.95/1.00    l1_waybel_0(sK1,sK0)),
% 1.95/1.00    inference(cnf_transformation,[],[f35])).
% 1.95/1.00  
% 1.95/1.00  fof(f54,plain,(
% 1.95/1.00    m1_yellow_6(sK3,sK0,sK2)),
% 1.95/1.00    inference(cnf_transformation,[],[f35])).
% 1.95/1.00  
% 1.95/1.00  fof(f7,axiom,(
% 1.95/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (l1_waybel_0(X2,X0) => (m1_yellow_6(X2,X0,X1) <=> (k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) = u1_waybel_0(X0,X2) & m1_yellow_0(X2,X1))))))),
% 1.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.00  
% 1.95/1.00  fof(f22,plain,(
% 1.95/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow_6(X2,X0,X1) <=> (k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) = u1_waybel_0(X0,X2) & m1_yellow_0(X2,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.95/1.00    inference(ennf_transformation,[],[f7])).
% 1.95/1.00  
% 1.95/1.00  fof(f29,plain,(
% 1.95/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | (k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) != u1_waybel_0(X0,X2) | ~m1_yellow_0(X2,X1))) & ((k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) = u1_waybel_0(X0,X2) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.95/1.00    inference(nnf_transformation,[],[f22])).
% 1.95/1.00  
% 1.95/1.00  fof(f30,plain,(
% 1.95/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) != u1_waybel_0(X0,X2) | ~m1_yellow_0(X2,X1)) & ((k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) = u1_waybel_0(X0,X2) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.95/1.00    inference(flattening,[],[f29])).
% 1.95/1.00  
% 1.95/1.00  fof(f47,plain,(
% 1.95/1.00    ( ! [X2,X0,X1] : (k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) = u1_waybel_0(X0,X2) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.95/1.00    inference(cnf_transformation,[],[f30])).
% 1.95/1.00  
% 1.95/1.00  fof(f6,axiom,(
% 1.95/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.00  
% 1.95/1.00  fof(f12,plain,(
% 1.95/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.95/1.00    inference(pure_predicate_removal,[],[f6])).
% 1.95/1.00  
% 1.95/1.00  fof(f20,plain,(
% 1.95/1.00    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 1.95/1.00    inference(ennf_transformation,[],[f12])).
% 1.95/1.00  
% 1.95/1.00  fof(f21,plain,(
% 1.95/1.00    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 1.95/1.00    inference(flattening,[],[f20])).
% 1.95/1.00  
% 1.95/1.00  fof(f45,plain,(
% 1.95/1.00    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.95/1.00    inference(cnf_transformation,[],[f21])).
% 1.95/1.00  
% 1.95/1.00  fof(f3,axiom,(
% 1.95/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 1.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.00  
% 1.95/1.00  fof(f16,plain,(
% 1.95/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.95/1.00    inference(ennf_transformation,[],[f3])).
% 1.95/1.00  
% 1.95/1.00  fof(f17,plain,(
% 1.95/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.95/1.00    inference(flattening,[],[f16])).
% 1.95/1.00  
% 1.95/1.00  fof(f39,plain,(
% 1.95/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.95/1.00    inference(cnf_transformation,[],[f17])).
% 1.95/1.00  
% 1.95/1.00  fof(f44,plain,(
% 1.95/1.00    ( ! [X0,X1] : (v1_funct_1(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.95/1.00    inference(cnf_transformation,[],[f21])).
% 1.95/1.00  
% 1.95/1.00  fof(f46,plain,(
% 1.95/1.00    ( ! [X2,X0,X1] : (m1_yellow_0(X2,X1) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.95/1.00    inference(cnf_transformation,[],[f30])).
% 1.95/1.00  
% 1.95/1.00  fof(f4,axiom,(
% 1.95/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 1.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.00  
% 1.95/1.00  fof(f18,plain,(
% 1.95/1.00    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 1.95/1.00    inference(ennf_transformation,[],[f4])).
% 1.95/1.00  
% 1.95/1.00  fof(f27,plain,(
% 1.95/1.00    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 1.95/1.00    inference(nnf_transformation,[],[f18])).
% 1.95/1.00  
% 1.95/1.00  fof(f28,plain,(
% 1.95/1.00    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 1.95/1.00    inference(flattening,[],[f27])).
% 1.95/1.00  
% 1.95/1.00  fof(f40,plain,(
% 1.95/1.00    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 1.95/1.00    inference(cnf_transformation,[],[f28])).
% 1.95/1.00  
% 1.95/1.00  fof(f1,axiom,(
% 1.95/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 1.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.00  
% 1.95/1.00  fof(f13,plain,(
% 1.95/1.00    ! [X0,X1,X2] : (((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) | ~r1_tarski(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.95/1.00    inference(ennf_transformation,[],[f1])).
% 1.95/1.00  
% 1.95/1.00  fof(f14,plain,(
% 1.95/1.00    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) | ~r1_tarski(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.95/1.00    inference(flattening,[],[f13])).
% 1.95/1.00  
% 1.95/1.00  fof(f37,plain,(
% 1.95/1.00    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.95/1.00    inference(cnf_transformation,[],[f14])).
% 1.95/1.00  
% 1.95/1.00  fof(f2,axiom,(
% 1.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.00  
% 1.95/1.00  fof(f15,plain,(
% 1.95/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/1.00    inference(ennf_transformation,[],[f2])).
% 1.95/1.00  
% 1.95/1.00  fof(f38,plain,(
% 1.95/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/1.00    inference(cnf_transformation,[],[f15])).
% 1.95/1.00  
% 1.95/1.00  fof(f5,axiom,(
% 1.95/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 1.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.00  
% 1.95/1.00  fof(f19,plain,(
% 1.95/1.00    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.95/1.00    inference(ennf_transformation,[],[f5])).
% 1.95/1.00  
% 1.95/1.00  fof(f43,plain,(
% 1.95/1.00    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.95/1.00    inference(cnf_transformation,[],[f19])).
% 1.95/1.00  
% 1.95/1.00  fof(f55,plain,(
% 1.95/1.00    ~m1_yellow_6(sK3,sK0,sK1)),
% 1.95/1.00    inference(cnf_transformation,[],[f35])).
% 1.95/1.00  
% 1.95/1.00  fof(f48,plain,(
% 1.95/1.00    ( ! [X2,X0,X1] : (m1_yellow_6(X2,X0,X1) | k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) != u1_waybel_0(X0,X2) | ~m1_yellow_0(X2,X1) | ~l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.95/1.00    inference(cnf_transformation,[],[f30])).
% 1.95/1.00  
% 1.95/1.00  fof(f9,axiom,(
% 1.95/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => ! [X2] : (m1_yellow_0(X2,X1) => m1_yellow_0(X2,X0))))),
% 1.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.00  
% 1.95/1.00  fof(f25,plain,(
% 1.95/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_yellow_0(X2,X0) | ~m1_yellow_0(X2,X1)) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 1.95/1.00    inference(ennf_transformation,[],[f9])).
% 1.95/1.00  
% 1.95/1.00  fof(f50,plain,(
% 1.95/1.00    ( ! [X2,X0,X1] : (m1_yellow_0(X2,X0) | ~m1_yellow_0(X2,X1) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 1.95/1.00    inference(cnf_transformation,[],[f25])).
% 1.95/1.00  
% 1.95/1.00  cnf(c_17,negated_conjecture,
% 1.95/1.00      ( m1_yellow_6(sK2,sK0,sK1) ),
% 1.95/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_13,plain,
% 1.95/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 1.95/1.00      | ~ l1_waybel_0(X2,X1)
% 1.95/1.00      | l1_waybel_0(X0,X1)
% 1.95/1.00      | ~ l1_struct_0(X1) ),
% 1.95/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_19,negated_conjecture,
% 1.95/1.00      ( l1_struct_0(sK0) ),
% 1.95/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_420,plain,
% 1.95/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 1.95/1.00      | ~ l1_waybel_0(X2,X1)
% 1.95/1.00      | l1_waybel_0(X0,X1)
% 1.95/1.00      | sK0 != X1 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_421,plain,
% 1.95/1.00      ( ~ m1_yellow_6(X0,sK0,X1)
% 1.95/1.00      | ~ l1_waybel_0(X1,sK0)
% 1.95/1.00      | l1_waybel_0(X0,sK0) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_420]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_773,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,sK0)
% 1.95/1.00      | l1_waybel_0(X1,sK0)
% 1.95/1.00      | sK2 != X1
% 1.95/1.00      | sK1 != X0
% 1.95/1.00      | sK0 != sK0 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_421]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_774,plain,
% 1.95/1.00      ( l1_waybel_0(sK2,sK0) | ~ l1_waybel_0(sK1,sK0) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_773]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_18,negated_conjecture,
% 1.95/1.00      ( l1_waybel_0(sK1,sK0) ),
% 1.95/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_776,plain,
% 1.95/1.00      ( l1_waybel_0(sK2,sK0) ),
% 1.95/1.00      inference(global_propositional_subsumption,
% 1.95/1.00                [status(thm)],
% 1.95/1.00                [c_774,c_18]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_16,negated_conjecture,
% 1.95/1.00      ( m1_yellow_6(sK3,sK0,sK2) ),
% 1.95/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_11,plain,
% 1.95/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 1.95/1.00      | ~ l1_waybel_0(X2,X1)
% 1.95/1.00      | ~ l1_waybel_0(X0,X1)
% 1.95/1.00      | ~ l1_struct_0(X1)
% 1.95/1.00      | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) = u1_waybel_0(X1,X0) ),
% 1.95/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_117,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X2,X1)
% 1.95/1.00      | ~ m1_yellow_6(X0,X1,X2)
% 1.95/1.00      | ~ l1_struct_0(X1)
% 1.95/1.00      | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) = u1_waybel_0(X1,X0) ),
% 1.95/1.00      inference(global_propositional_subsumption,
% 1.95/1.00                [status(thm)],
% 1.95/1.00                [c_11,c_13]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_118,plain,
% 1.95/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 1.95/1.00      | ~ l1_waybel_0(X2,X1)
% 1.95/1.00      | ~ l1_struct_0(X1)
% 1.95/1.00      | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) = u1_waybel_0(X1,X0) ),
% 1.95/1.00      inference(renaming,[status(thm)],[c_117]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_390,plain,
% 1.95/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 1.95/1.00      | ~ l1_waybel_0(X2,X1)
% 1.95/1.00      | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) = u1_waybel_0(X1,X0)
% 1.95/1.00      | sK0 != X1 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_118,c_19]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_391,plain,
% 1.95/1.00      ( ~ m1_yellow_6(X0,sK0,X1)
% 1.95/1.00      | ~ l1_waybel_0(X1,sK0)
% 1.95/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1),u1_struct_0(X0)) = u1_waybel_0(sK0,X0) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_390]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_763,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,sK0)
% 1.95/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0),u1_struct_0(X1)) = u1_waybel_0(sK0,X1)
% 1.95/1.00      | sK2 != X0
% 1.95/1.00      | sK0 != sK0
% 1.95/1.00      | sK3 != X1 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_391]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_764,plain,
% 1.95/1.00      ( ~ l1_waybel_0(sK2,sK0)
% 1.95/1.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) = u1_waybel_0(sK0,sK3) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_763]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_783,plain,
% 1.95/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) = u1_waybel_0(sK0,sK3) ),
% 1.95/1.00      inference(backward_subsumption_resolution,
% 1.95/1.00                [status(thm)],
% 1.95/1.00                [c_776,c_764]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1326,plain,
% 1.95/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) = u1_waybel_0(sK0,sK3) ),
% 1.95/1.00      inference(subtyping,[status(esa)],[c_783]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_8,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,X1)
% 1.95/1.00      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.95/1.00      | ~ l1_struct_0(X1) ),
% 1.95/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_466,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,X1)
% 1.95/1.00      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.95/1.00      | sK0 != X1 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_467,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,sK0)
% 1.95/1.00      | m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_466]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_985,plain,
% 1.95/1.00      ( m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
% 1.95/1.00      | sK2 != X0
% 1.95/1.00      | sK0 != sK0 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_467,c_776]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_986,plain,
% 1.95/1.00      ( m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_985]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1307,plain,
% 1.95/1.00      ( m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
% 1.95/1.00      inference(subtyping,[status(esa)],[c_986]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1805,plain,
% 1.95/1.00      ( m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) = iProver_top ),
% 1.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1307]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_3,plain,
% 1.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/1.00      | ~ v1_funct_1(X0)
% 1.95/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 1.95/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_9,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,X1)
% 1.95/1.00      | ~ l1_struct_0(X1)
% 1.95/1.00      | v1_funct_1(u1_waybel_0(X1,X0)) ),
% 1.95/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_454,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,X1)
% 1.95/1.00      | v1_funct_1(u1_waybel_0(X1,X0))
% 1.95/1.00      | sK0 != X1 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_455,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,sK0) | v1_funct_1(u1_waybel_0(sK0,X0)) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_454]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_559,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,sK0)
% 1.95/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.95/1.00      | k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
% 1.95/1.00      | u1_waybel_0(sK0,X0) != X1 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_455]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_560,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,sK0)
% 1.95/1.00      | ~ m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/1.00      | k2_partfun1(X1,X2,u1_waybel_0(sK0,X0),X3) = k7_relat_1(u1_waybel_0(sK0,X0),X3) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_559]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_966,plain,
% 1.95/1.00      ( ~ m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/1.00      | k2_partfun1(X1,X2,u1_waybel_0(sK0,X0),X3) = k7_relat_1(u1_waybel_0(sK0,X0),X3)
% 1.95/1.00      | sK2 != X0
% 1.95/1.00      | sK0 != sK0 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_560,c_776]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_967,plain,
% 1.95/1.00      ( ~ m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.95/1.00      | k2_partfun1(X0,X1,u1_waybel_0(sK0,sK2),X2) = k7_relat_1(u1_waybel_0(sK0,sK2),X2) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_966]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1309,plain,
% 1.95/1.00      ( ~ m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.95/1.00      | k2_partfun1(X0_52,X1_52,u1_waybel_0(sK0,sK2),X2_52) = k7_relat_1(u1_waybel_0(sK0,sK2),X2_52) ),
% 1.95/1.00      inference(subtyping,[status(esa)],[c_967]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1803,plain,
% 1.95/1.00      ( k2_partfun1(X0_52,X1_52,u1_waybel_0(sK0,sK2),X2_52) = k7_relat_1(u1_waybel_0(sK0,sK2),X2_52)
% 1.95/1.00      | m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 1.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1309]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_2662,plain,
% 1.95/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2),X0_52) = k7_relat_1(u1_waybel_0(sK0,sK2),X0_52) ),
% 1.95/1.00      inference(superposition,[status(thm)],[c_1805,c_1803]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_3208,plain,
% 1.95/1.00      ( k7_relat_1(u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) = u1_waybel_0(sK0,sK3) ),
% 1.95/1.00      inference(superposition,[status(thm)],[c_1326,c_2662]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_12,plain,
% 1.95/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 1.95/1.00      | ~ l1_waybel_0(X2,X1)
% 1.95/1.00      | ~ l1_waybel_0(X0,X1)
% 1.95/1.00      | m1_yellow_0(X0,X2)
% 1.95/1.00      | ~ l1_struct_0(X1) ),
% 1.95/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_112,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X2,X1)
% 1.95/1.00      | ~ m1_yellow_6(X0,X1,X2)
% 1.95/1.00      | m1_yellow_0(X0,X2)
% 1.95/1.00      | ~ l1_struct_0(X1) ),
% 1.95/1.00      inference(global_propositional_subsumption,
% 1.95/1.00                [status(thm)],
% 1.95/1.00                [c_12,c_13]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_113,plain,
% 1.95/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 1.95/1.00      | ~ l1_waybel_0(X2,X1)
% 1.95/1.00      | m1_yellow_0(X0,X2)
% 1.95/1.00      | ~ l1_struct_0(X1) ),
% 1.95/1.00      inference(renaming,[status(thm)],[c_112]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_405,plain,
% 1.95/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 1.95/1.00      | ~ l1_waybel_0(X2,X1)
% 1.95/1.00      | m1_yellow_0(X0,X2)
% 1.95/1.00      | sK0 != X1 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_113,c_19]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_406,plain,
% 1.95/1.00      ( ~ m1_yellow_6(X0,sK0,X1)
% 1.95/1.00      | ~ l1_waybel_0(X1,sK0)
% 1.95/1.00      | m1_yellow_0(X0,X1) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_405]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_753,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,sK0)
% 1.95/1.00      | m1_yellow_0(X1,X0)
% 1.95/1.00      | sK2 != X0
% 1.95/1.00      | sK0 != sK0
% 1.95/1.00      | sK3 != X1 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_406]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_754,plain,
% 1.95/1.00      ( ~ l1_waybel_0(sK2,sK0) | m1_yellow_0(sK3,sK2) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_753]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_785,plain,
% 1.95/1.00      ( m1_yellow_0(sK3,sK2) ),
% 1.95/1.00      inference(backward_subsumption_resolution,
% 1.95/1.00                [status(thm)],
% 1.95/1.00                [c_776,c_754]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1325,plain,
% 1.95/1.00      ( m1_yellow_0(sK3,sK2) ),
% 1.95/1.00      inference(subtyping,[status(esa)],[c_785]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1788,plain,
% 1.95/1.00      ( m1_yellow_0(sK3,sK2) = iProver_top ),
% 1.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1325]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_6,plain,
% 1.95/1.00      ( ~ m1_yellow_0(X0,X1)
% 1.95/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 1.95/1.00      | ~ l1_orders_2(X0)
% 1.95/1.00      | ~ l1_orders_2(X1) ),
% 1.95/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1330,plain,
% 1.95/1.00      ( ~ m1_yellow_0(X0_50,X1_50)
% 1.95/1.00      | r1_tarski(u1_struct_0(X0_50),u1_struct_0(X1_50))
% 1.95/1.00      | ~ l1_orders_2(X1_50)
% 1.95/1.00      | ~ l1_orders_2(X0_50) ),
% 1.95/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1786,plain,
% 1.95/1.00      ( m1_yellow_0(X0_50,X1_50) != iProver_top
% 1.95/1.00      | r1_tarski(u1_struct_0(X0_50),u1_struct_0(X1_50)) = iProver_top
% 1.95/1.00      | l1_orders_2(X1_50) != iProver_top
% 1.95/1.00      | l1_orders_2(X0_50) != iProver_top ),
% 1.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_0,plain,
% 1.95/1.00      ( ~ r1_tarski(X0,X1)
% 1.95/1.00      | ~ v1_relat_1(X2)
% 1.95/1.00      | ~ v1_funct_1(X2)
% 1.95/1.00      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
% 1.95/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_592,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,sK0)
% 1.95/1.00      | ~ r1_tarski(X1,X2)
% 1.95/1.00      | ~ v1_relat_1(X3)
% 1.95/1.00      | u1_waybel_0(sK0,X0) != X3
% 1.95/1.00      | k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_455]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_593,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,sK0)
% 1.95/1.00      | ~ r1_tarski(X1,X2)
% 1.95/1.00      | ~ v1_relat_1(u1_waybel_0(sK0,X0))
% 1.95/1.00      | k7_relat_1(k7_relat_1(u1_waybel_0(sK0,X0),X2),X1) = k7_relat_1(u1_waybel_0(sK0,X0),X1) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_592]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_830,plain,
% 1.95/1.00      ( ~ r1_tarski(X0,X1)
% 1.95/1.00      | ~ v1_relat_1(u1_waybel_0(sK0,X2))
% 1.95/1.00      | k7_relat_1(k7_relat_1(u1_waybel_0(sK0,X2),X1),X0) = k7_relat_1(u1_waybel_0(sK0,X2),X0)
% 1.95/1.00      | sK1 != X2
% 1.95/1.00      | sK0 != sK0 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_593]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_831,plain,
% 1.95/1.00      ( ~ r1_tarski(X0,X1)
% 1.95/1.00      | ~ v1_relat_1(u1_waybel_0(sK0,sK1))
% 1.95/1.00      | k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),X1),X0) = k7_relat_1(u1_waybel_0(sK0,sK1),X0) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_830]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1321,plain,
% 1.95/1.00      ( ~ r1_tarski(X0_52,X1_52)
% 1.95/1.00      | ~ v1_relat_1(u1_waybel_0(sK0,sK1))
% 1.95/1.00      | k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),X1_52),X0_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X0_52) ),
% 1.95/1.00      inference(subtyping,[status(esa)],[c_831]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1791,plain,
% 1.95/1.00      ( k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),X0_52),X1_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X1_52)
% 1.95/1.00      | r1_tarski(X1_52,X0_52) != iProver_top
% 1.95/1.00      | v1_relat_1(u1_waybel_0(sK0,sK1)) != iProver_top ),
% 1.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_877,plain,
% 1.95/1.00      ( m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
% 1.95/1.00      | sK1 != X0
% 1.95/1.00      | sK0 != sK0 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_467]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_878,plain,
% 1.95/1.00      ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_877]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_879,plain,
% 1.95/1.00      ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 1.95/1.00      inference(predicate_to_equality,[status(thm)],[c_878]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1380,plain,
% 1.95/1.00      ( k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),X0_52),X1_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X1_52)
% 1.95/1.00      | r1_tarski(X1_52,X0_52) != iProver_top
% 1.95/1.00      | v1_relat_1(u1_waybel_0(sK0,sK1)) != iProver_top ),
% 1.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_2,plain,
% 1.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/1.00      | v1_relat_1(X0) ),
% 1.95/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1333,plain,
% 1.95/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.95/1.00      | v1_relat_1(X0_48) ),
% 1.95/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1976,plain,
% 1.95/1.00      ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.95/1.00      | v1_relat_1(u1_waybel_0(sK0,sK1)) ),
% 1.95/1.00      inference(instantiation,[status(thm)],[c_1333]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1977,plain,
% 1.95/1.00      ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 1.95/1.00      | v1_relat_1(u1_waybel_0(sK0,sK1)) = iProver_top ),
% 1.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1976]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_2249,plain,
% 1.95/1.00      ( r1_tarski(X1_52,X0_52) != iProver_top
% 1.95/1.00      | k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),X0_52),X1_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X1_52) ),
% 1.95/1.00      inference(global_propositional_subsumption,
% 1.95/1.00                [status(thm)],
% 1.95/1.00                [c_1791,c_879,c_1380,c_1977]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_2250,plain,
% 1.95/1.00      ( k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),X0_52),X1_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X1_52)
% 1.95/1.00      | r1_tarski(X1_52,X0_52) != iProver_top ),
% 1.95/1.00      inference(renaming,[status(thm)],[c_2249]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_2257,plain,
% 1.95/1.00      ( k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(X0_50)),u1_struct_0(X1_50)) = k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(X1_50))
% 1.95/1.00      | m1_yellow_0(X1_50,X0_50) != iProver_top
% 1.95/1.00      | l1_orders_2(X0_50) != iProver_top
% 1.95/1.00      | l1_orders_2(X1_50) != iProver_top ),
% 1.95/1.00      inference(superposition,[status(thm)],[c_1786,c_2250]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_2808,plain,
% 1.95/1.00      ( k7_relat_1(k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK2)),u1_struct_0(sK3)) = k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3))
% 1.95/1.00      | l1_orders_2(sK2) != iProver_top
% 1.95/1.00      | l1_orders_2(sK3) != iProver_top ),
% 1.95/1.00      inference(superposition,[status(thm)],[c_1788,c_2257]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_800,plain,
% 1.95/1.00      ( ~ l1_waybel_0(X0,sK0)
% 1.95/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0),u1_struct_0(X1)) = u1_waybel_0(sK0,X1)
% 1.95/1.00      | sK2 != X1
% 1.95/1.00      | sK1 != X0
% 1.95/1.00      | sK0 != sK0 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_391]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_801,plain,
% 1.95/1.00      ( ~ l1_waybel_0(sK1,sK0)
% 1.95/1.00      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK2)) = u1_waybel_0(sK0,sK2) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_800]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_803,plain,
% 1.95/1.00      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK2)) = u1_waybel_0(sK0,sK2) ),
% 1.95/1.00      inference(global_propositional_subsumption,
% 1.95/1.00                [status(thm)],
% 1.95/1.00                [c_801,c_18]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1323,plain,
% 1.95/1.00      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK2)) = u1_waybel_0(sK0,sK2) ),
% 1.95/1.00      inference(subtyping,[status(esa)],[c_803]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1317,plain,
% 1.95/1.00      ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 1.95/1.00      inference(subtyping,[status(esa)],[c_878]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1795,plain,
% 1.95/1.00      ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 1.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1317]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_858,plain,
% 1.95/1.00      ( ~ m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.95/1.00      | k2_partfun1(X1,X2,u1_waybel_0(sK0,X0),X3) = k7_relat_1(u1_waybel_0(sK0,X0),X3)
% 1.95/1.00      | sK1 != X0
% 1.95/1.00      | sK0 != sK0 ),
% 1.95/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_560]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_859,plain,
% 1.95/1.00      ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.95/1.00      | k2_partfun1(X0,X1,u1_waybel_0(sK0,sK1),X2) = k7_relat_1(u1_waybel_0(sK0,sK1),X2) ),
% 1.95/1.00      inference(unflattening,[status(thm)],[c_858]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1319,plain,
% 1.95/1.00      ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.95/1.00      | k2_partfun1(X0_52,X1_52,u1_waybel_0(sK0,sK1),X2_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X2_52) ),
% 1.95/1.00      inference(subtyping,[status(esa)],[c_859]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_1793,plain,
% 1.95/1.00      ( k2_partfun1(X0_52,X1_52,u1_waybel_0(sK0,sK1),X2_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X2_52)
% 1.95/1.00      | m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 1.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_2083,plain,
% 1.95/1.00      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0_52) = k7_relat_1(u1_waybel_0(sK0,sK1),X0_52) ),
% 1.95/1.00      inference(superposition,[status(thm)],[c_1795,c_1793]) ).
% 1.95/1.00  
% 1.95/1.00  cnf(c_2535,plain,
% 1.95/1.00      ( k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK2)) = u1_waybel_0(sK0,sK2) ),
% 1.95/1.01      inference(superposition,[status(thm)],[c_1323,c_2083]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2820,plain,
% 1.95/1.01      ( k7_relat_1(u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) = k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3))
% 1.95/1.01      | l1_orders_2(sK2) != iProver_top
% 1.95/1.01      | l1_orders_2(sK3) != iProver_top ),
% 1.95/1.01      inference(light_normalisation,[status(thm)],[c_2808,c_2535]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_7,plain,
% 1.95/1.01      ( ~ l1_waybel_0(X0,X1) | ~ l1_struct_0(X1) | l1_orders_2(X0) ),
% 1.95/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_478,plain,
% 1.95/1.01      ( ~ l1_waybel_0(X0,X1) | l1_orders_2(X0) | sK0 != X1 ),
% 1.95/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_479,plain,
% 1.95/1.01      ( ~ l1_waybel_0(X0,sK0) | l1_orders_2(X0) ),
% 1.95/1.01      inference(unflattening,[status(thm)],[c_478]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_743,plain,
% 1.95/1.01      ( ~ l1_waybel_0(X0,sK0)
% 1.95/1.01      | l1_waybel_0(X1,sK0)
% 1.95/1.01      | sK2 != X0
% 1.95/1.01      | sK0 != sK0
% 1.95/1.01      | sK3 != X1 ),
% 1.95/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_421]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_744,plain,
% 1.95/1.01      ( ~ l1_waybel_0(sK2,sK0) | l1_waybel_0(sK3,sK0) ),
% 1.95/1.01      inference(unflattening,[status(thm)],[c_743]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_784,plain,
% 1.95/1.01      ( l1_waybel_0(sK3,sK0) ),
% 1.95/1.01      inference(backward_subsumption_resolution,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_776,c_744]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_924,plain,
% 1.95/1.01      ( l1_orders_2(X0) | sK0 != sK0 | sK3 != X0 ),
% 1.95/1.01      inference(resolution_lifted,[status(thm)],[c_479,c_784]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_925,plain,
% 1.95/1.01      ( l1_orders_2(sK3) ),
% 1.95/1.01      inference(unflattening,[status(thm)],[c_924]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_926,plain,
% 1.95/1.01      ( l1_orders_2(sK3) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_925]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_978,plain,
% 1.95/1.01      ( l1_orders_2(X0) | sK2 != X0 | sK0 != sK0 ),
% 1.95/1.01      inference(resolution_lifted,[status(thm)],[c_479,c_776]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_979,plain,
% 1.95/1.01      ( l1_orders_2(sK2) ),
% 1.95/1.01      inference(unflattening,[status(thm)],[c_978]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_980,plain,
% 1.95/1.01      ( l1_orders_2(sK2) = iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_979]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2886,plain,
% 1.95/1.01      ( k7_relat_1(u1_waybel_0(sK0,sK2),u1_struct_0(sK3)) = k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) ),
% 1.95/1.01      inference(global_propositional_subsumption,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_2820,c_926,c_980]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_3211,plain,
% 1.95/1.01      ( k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) = u1_waybel_0(sK0,sK3) ),
% 1.95/1.01      inference(demodulation,[status(thm)],[c_3208,c_2886]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_15,negated_conjecture,
% 1.95/1.01      ( ~ m1_yellow_6(sK3,sK0,sK1) ),
% 1.95/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_10,plain,
% 1.95/1.01      ( m1_yellow_6(X0,X1,X2)
% 1.95/1.01      | ~ l1_waybel_0(X2,X1)
% 1.95/1.01      | ~ l1_waybel_0(X0,X1)
% 1.95/1.01      | ~ m1_yellow_0(X0,X2)
% 1.95/1.01      | ~ l1_struct_0(X1)
% 1.95/1.01      | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) != u1_waybel_0(X1,X0) ),
% 1.95/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_433,plain,
% 1.95/1.01      ( m1_yellow_6(X0,X1,X2)
% 1.95/1.01      | ~ l1_waybel_0(X2,X1)
% 1.95/1.01      | ~ l1_waybel_0(X0,X1)
% 1.95/1.01      | ~ m1_yellow_0(X0,X2)
% 1.95/1.01      | k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X0)) != u1_waybel_0(X1,X0)
% 1.95/1.01      | sK0 != X1 ),
% 1.95/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_434,plain,
% 1.95/1.01      ( m1_yellow_6(X0,sK0,X1)
% 1.95/1.01      | ~ l1_waybel_0(X1,sK0)
% 1.95/1.01      | ~ l1_waybel_0(X0,sK0)
% 1.95/1.01      | ~ m1_yellow_0(X0,X1)
% 1.95/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1),u1_struct_0(X0)) != u1_waybel_0(sK0,X0) ),
% 1.95/1.01      inference(unflattening,[status(thm)],[c_433]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_726,plain,
% 1.95/1.01      ( ~ l1_waybel_0(X0,sK0)
% 1.95/1.01      | ~ l1_waybel_0(X1,sK0)
% 1.95/1.01      | ~ m1_yellow_0(X1,X0)
% 1.95/1.01      | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0),u1_struct_0(X1)) != u1_waybel_0(sK0,X1)
% 1.95/1.01      | sK1 != X0
% 1.95/1.01      | sK0 != sK0
% 1.95/1.01      | sK3 != X1 ),
% 1.95/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_434]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_727,plain,
% 1.95/1.01      ( ~ l1_waybel_0(sK1,sK0)
% 1.95/1.01      | ~ l1_waybel_0(sK3,sK0)
% 1.95/1.01      | ~ m1_yellow_0(sK3,sK1)
% 1.95/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3) ),
% 1.95/1.01      inference(unflattening,[status(thm)],[c_726]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_729,plain,
% 1.95/1.01      ( ~ l1_waybel_0(sK3,sK0)
% 1.95/1.01      | ~ m1_yellow_0(sK3,sK1)
% 1.95/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3) ),
% 1.95/1.01      inference(global_propositional_subsumption,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_727,c_18]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_822,plain,
% 1.95/1.01      ( ~ m1_yellow_0(sK3,sK1)
% 1.95/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3) ),
% 1.95/1.01      inference(backward_subsumption_resolution,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_784,c_729]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1322,plain,
% 1.95/1.01      ( ~ m1_yellow_0(sK3,sK1)
% 1.95/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3) ),
% 1.95/1.01      inference(subtyping,[status(esa)],[c_822]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1790,plain,
% 1.95/1.01      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3)
% 1.95/1.01      | m1_yellow_0(sK3,sK1) != iProver_top ),
% 1.95/1.01      inference(predicate_to_equality,[status(thm)],[c_1322]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_789,plain,
% 1.95/1.01      ( ~ l1_waybel_0(X0,sK0)
% 1.95/1.01      | m1_yellow_0(X1,X0)
% 1.95/1.01      | sK2 != X1
% 1.95/1.01      | sK1 != X0
% 1.95/1.01      | sK0 != sK0 ),
% 1.95/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_406]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_790,plain,
% 1.95/1.01      ( ~ l1_waybel_0(sK1,sK0) | m1_yellow_0(sK2,sK1) ),
% 1.95/1.01      inference(unflattening,[status(thm)],[c_789]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_870,plain,
% 1.95/1.01      ( l1_orders_2(X0) | sK1 != X0 | sK0 != sK0 ),
% 1.95/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_479]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_871,plain,
% 1.95/1.01      ( l1_orders_2(sK1) ),
% 1.95/1.01      inference(unflattening,[status(thm)],[c_870]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_14,plain,
% 1.95/1.01      ( ~ m1_yellow_0(X0,X1)
% 1.95/1.01      | ~ m1_yellow_0(X2,X0)
% 1.95/1.01      | m1_yellow_0(X2,X1)
% 1.95/1.01      | ~ l1_orders_2(X1) ),
% 1.95/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_1329,plain,
% 1.95/1.01      ( ~ m1_yellow_0(X0_50,X1_50)
% 1.95/1.01      | ~ m1_yellow_0(X2_50,X0_50)
% 1.95/1.01      | m1_yellow_0(X2_50,X1_50)
% 1.95/1.01      | ~ l1_orders_2(X1_50) ),
% 1.95/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2055,plain,
% 1.95/1.01      ( ~ m1_yellow_0(X0_50,X1_50)
% 1.95/1.01      | ~ m1_yellow_0(X1_50,sK1)
% 1.95/1.01      | m1_yellow_0(X0_50,sK1)
% 1.95/1.01      | ~ l1_orders_2(sK1) ),
% 1.95/1.01      inference(instantiation,[status(thm)],[c_1329]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2368,plain,
% 1.95/1.01      ( ~ m1_yellow_0(X0_50,sK2)
% 1.95/1.01      | m1_yellow_0(X0_50,sK1)
% 1.95/1.01      | ~ m1_yellow_0(sK2,sK1)
% 1.95/1.01      | ~ l1_orders_2(sK1) ),
% 1.95/1.01      inference(instantiation,[status(thm)],[c_2055]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2531,plain,
% 1.95/1.01      ( ~ m1_yellow_0(sK2,sK1)
% 1.95/1.01      | ~ m1_yellow_0(sK3,sK2)
% 1.95/1.01      | m1_yellow_0(sK3,sK1)
% 1.95/1.01      | ~ l1_orders_2(sK1) ),
% 1.95/1.01      inference(instantiation,[status(thm)],[c_2368]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2538,plain,
% 1.95/1.01      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3) ),
% 1.95/1.01      inference(global_propositional_subsumption,
% 1.95/1.01                [status(thm)],
% 1.95/1.01                [c_1790,c_18,c_754,c_774,c_790,c_871,c_1322,c_2531]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(c_2540,plain,
% 1.95/1.01      ( k7_relat_1(u1_waybel_0(sK0,sK1),u1_struct_0(sK3)) != u1_waybel_0(sK0,sK3) ),
% 1.95/1.01      inference(demodulation,[status(thm)],[c_2538,c_2083]) ).
% 1.95/1.01  
% 1.95/1.01  cnf(contradiction,plain,
% 1.95/1.01      ( $false ),
% 1.95/1.01      inference(minisat,[status(thm)],[c_3211,c_2540]) ).
% 1.95/1.01  
% 1.95/1.01  
% 1.95/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.95/1.01  
% 1.95/1.01  ------                               Statistics
% 1.95/1.01  
% 1.95/1.01  ------ General
% 1.95/1.01  
% 1.95/1.01  abstr_ref_over_cycles:                  0
% 1.95/1.01  abstr_ref_under_cycles:                 0
% 1.95/1.01  gc_basic_clause_elim:                   0
% 1.95/1.01  forced_gc_time:                         0
% 1.95/1.01  parsing_time:                           0.009
% 1.95/1.01  unif_index_cands_time:                  0.
% 1.95/1.01  unif_index_add_time:                    0.
% 1.95/1.01  orderings_time:                         0.
% 1.95/1.01  out_proof_time:                         0.01
% 1.95/1.01  total_time:                             0.12
% 1.95/1.01  num_of_symbols:                         53
% 1.95/1.01  num_of_terms:                           2548
% 1.95/1.01  
% 1.95/1.01  ------ Preprocessing
% 1.95/1.01  
% 1.95/1.01  num_of_splits:                          0
% 1.95/1.01  num_of_split_atoms:                     0
% 1.95/1.01  num_of_reused_defs:                     0
% 1.95/1.01  num_eq_ax_congr_red:                    11
% 1.95/1.01  num_of_sem_filtered_clauses:            1
% 1.95/1.01  num_of_subtypes:                        5
% 1.95/1.01  monotx_restored_types:                  0
% 1.95/1.01  sat_num_of_epr_types:                   0
% 1.95/1.01  sat_num_of_non_cyclic_types:            0
% 1.95/1.01  sat_guarded_non_collapsed_types:        0
% 1.95/1.01  num_pure_diseq_elim:                    0
% 1.95/1.01  simp_replaced_by:                       0
% 1.95/1.01  res_preprocessed:                       111
% 1.95/1.01  prep_upred:                             0
% 1.95/1.01  prep_unflattend:                        60
% 1.95/1.01  smt_new_axioms:                         0
% 1.95/1.01  pred_elim_cands:                        9
% 1.95/1.01  pred_elim:                              4
% 1.95/1.01  pred_elim_cl:                           -7
% 1.95/1.01  pred_elim_cycles:                       12
% 1.95/1.01  merged_defs:                            0
% 1.95/1.01  merged_defs_ncl:                        0
% 1.95/1.01  bin_hyper_res:                          0
% 1.95/1.01  prep_cycles:                            3
% 1.95/1.01  pred_elim_time:                         0.019
% 1.95/1.01  splitting_time:                         0.
% 1.95/1.01  sem_filter_time:                        0.
% 1.95/1.01  monotx_time:                            0.
% 1.95/1.01  subtype_inf_time:                       0.001
% 1.95/1.01  
% 1.95/1.01  ------ Problem properties
% 1.95/1.01  
% 1.95/1.01  clauses:                                27
% 1.95/1.01  conjectures:                            0
% 1.95/1.01  epr:                                    8
% 1.95/1.01  horn:                                   27
% 1.95/1.01  ground:                                 13
% 1.95/1.01  unary:                                  10
% 1.95/1.01  binary:                                 5
% 1.95/1.01  lits:                                   61
% 1.95/1.01  lits_eq:                                18
% 1.95/1.01  fd_pure:                                0
% 1.95/1.01  fd_pseudo:                              0
% 1.95/1.01  fd_cond:                                0
% 1.95/1.01  fd_pseudo_cond:                         0
% 1.95/1.01  ac_symbols:                             0
% 1.95/1.01  
% 1.95/1.01  ------ Propositional Solver
% 1.95/1.01  
% 1.95/1.01  prop_solver_calls:                      22
% 1.95/1.01  prop_fast_solver_calls:                 867
% 1.95/1.01  smt_solver_calls:                       0
% 1.95/1.01  smt_fast_solver_calls:                  0
% 1.95/1.01  prop_num_of_clauses:                    951
% 1.95/1.01  prop_preprocess_simplified:             3614
% 1.95/1.01  prop_fo_subsumed:                       26
% 1.95/1.01  prop_solver_time:                       0.
% 1.95/1.01  smt_solver_time:                        0.
% 1.95/1.01  smt_fast_solver_time:                   0.
% 1.95/1.01  prop_fast_solver_time:                  0.
% 1.95/1.01  prop_unsat_core_time:                   0.
% 1.95/1.01  
% 1.95/1.01  ------ QBF
% 1.95/1.01  
% 1.95/1.01  qbf_q_res:                              0
% 1.95/1.01  qbf_num_tautologies:                    0
% 1.95/1.01  qbf_prep_cycles:                        0
% 1.95/1.01  
% 1.95/1.01  ------ BMC1
% 1.95/1.01  
% 1.95/1.01  bmc1_current_bound:                     -1
% 1.95/1.01  bmc1_last_solved_bound:                 -1
% 1.95/1.01  bmc1_unsat_core_size:                   -1
% 1.95/1.01  bmc1_unsat_core_parents_size:           -1
% 1.95/1.01  bmc1_merge_next_fun:                    0
% 1.95/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.95/1.01  
% 1.95/1.01  ------ Instantiation
% 1.95/1.01  
% 1.95/1.01  inst_num_of_clauses:                    243
% 1.95/1.01  inst_num_in_passive:                    36
% 1.95/1.01  inst_num_in_active:                     207
% 1.95/1.01  inst_num_in_unprocessed:                0
% 1.95/1.01  inst_num_of_loops:                      220
% 1.95/1.01  inst_num_of_learning_restarts:          0
% 1.95/1.01  inst_num_moves_active_passive:          10
% 1.95/1.01  inst_lit_activity:                      0
% 1.95/1.01  inst_lit_activity_moves:                0
% 1.95/1.01  inst_num_tautologies:                   0
% 1.95/1.01  inst_num_prop_implied:                  0
% 1.95/1.01  inst_num_existing_simplified:           0
% 1.95/1.01  inst_num_eq_res_simplified:             0
% 1.95/1.01  inst_num_child_elim:                    0
% 1.95/1.01  inst_num_of_dismatching_blockings:      9
% 1.95/1.01  inst_num_of_non_proper_insts:           174
% 1.95/1.01  inst_num_of_duplicates:                 0
% 1.95/1.01  inst_inst_num_from_inst_to_res:         0
% 1.95/1.01  inst_dismatching_checking_time:         0.
% 1.95/1.01  
% 1.95/1.01  ------ Resolution
% 1.95/1.01  
% 1.95/1.01  res_num_of_clauses:                     0
% 1.95/1.01  res_num_in_passive:                     0
% 1.95/1.01  res_num_in_active:                      0
% 1.95/1.01  res_num_of_loops:                       114
% 1.95/1.01  res_forward_subset_subsumed:            29
% 1.95/1.01  res_backward_subset_subsumed:           0
% 1.95/1.01  res_forward_subsumed:                   0
% 1.95/1.01  res_backward_subsumed:                  0
% 1.95/1.01  res_forward_subsumption_resolution:     0
% 1.95/1.01  res_backward_subsumption_resolution:    4
% 1.95/1.01  res_clause_to_clause_subsumption:       95
% 1.95/1.01  res_orphan_elimination:                 0
% 1.95/1.01  res_tautology_del:                      36
% 1.95/1.01  res_num_eq_res_simplified:              2
% 1.95/1.01  res_num_sel_changes:                    0
% 1.95/1.01  res_moves_from_active_to_pass:          0
% 1.95/1.01  
% 1.95/1.01  ------ Superposition
% 1.95/1.01  
% 1.95/1.01  sup_time_total:                         0.
% 1.95/1.01  sup_time_generating:                    0.
% 1.95/1.01  sup_time_sim_full:                      0.
% 1.95/1.01  sup_time_sim_immed:                     0.
% 1.95/1.01  
% 1.95/1.01  sup_num_of_clauses:                     61
% 1.95/1.01  sup_num_in_active:                      42
% 1.95/1.01  sup_num_in_passive:                     19
% 1.95/1.01  sup_num_of_loops:                       43
% 1.95/1.01  sup_fw_superposition:                   27
% 1.95/1.01  sup_bw_superposition:                   9
% 1.95/1.01  sup_immediate_simplified:               3
% 1.95/1.01  sup_given_eliminated:                   0
% 1.95/1.01  comparisons_done:                       0
% 1.95/1.01  comparisons_avoided:                    0
% 1.95/1.01  
% 1.95/1.01  ------ Simplifications
% 1.95/1.01  
% 1.95/1.01  
% 1.95/1.01  sim_fw_subset_subsumed:                 0
% 1.95/1.01  sim_bw_subset_subsumed:                 0
% 1.95/1.01  sim_fw_subsumed:                        0
% 1.95/1.01  sim_bw_subsumed:                        0
% 1.95/1.01  sim_fw_subsumption_res:                 0
% 1.95/1.01  sim_bw_subsumption_res:                 0
% 1.95/1.01  sim_tautology_del:                      1
% 1.95/1.01  sim_eq_tautology_del:                   0
% 1.95/1.01  sim_eq_res_simp:                        2
% 1.95/1.01  sim_fw_demodulated:                     1
% 1.95/1.01  sim_bw_demodulated:                     1
% 1.95/1.01  sim_light_normalised:                   3
% 1.95/1.01  sim_joinable_taut:                      0
% 1.95/1.01  sim_joinable_simp:                      0
% 1.95/1.01  sim_ac_normalised:                      0
% 1.95/1.01  sim_smt_subsumption:                    0
% 1.95/1.01  
%------------------------------------------------------------------------------
