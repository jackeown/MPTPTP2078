%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:17 EST 2020

% Result     : CounterSatisfiable 0.73s
% Output     : Saturation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 808 expanded)
%              Number of clauses        :   60 ( 228 expanded)
%              Number of leaves         :   20 ( 223 expanded)
%              Depth                    :   22
%              Number of atoms          :  376 (6482 expanded)
%              Number of equality atoms :   97 ( 794 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,conjecture,(
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
               => ( k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0)
                  & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
                 => ( k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0)
                    & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
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
               => ( k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0)
                  & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
            | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k2_funct_1(X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(X0)
          | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X1),u1_struct_0(X0))
          | ~ v1_funct_1(k2_funct_1(sK2)) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
              | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
              | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(sK1),u1_struct_0(X0))
              | ~ v1_funct_1(k2_funct_1(X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_orders_2(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
                  | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(k2_funct_1(X2)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK0)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f28,f27,f26])).

fof(f44,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f46,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_162,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_161,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_159,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_158,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_157,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_156,plain,
    ( ~ v1_partfun1(X0,X1)
    | v1_partfun1(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_155,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_153,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_469,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_264,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_265,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_14,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_181,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_182,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_210,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_182])).

cnf(c_211,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_267,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_265,c_14,c_12,c_10,c_211])).

cnf(c_6,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_336,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_337,plain,
    ( v4_relat_1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_372,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_relat_1(X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_337])).

cnf(c_373,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_414,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK0) != X0
    | k1_relat_1(sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_267,c_373])).

cnf(c_415,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = u1_struct_0(sK0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_463,plain,
    ( ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_48))
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_415])).

cnf(c_468,plain,
    ( ~ v1_relat_1(sK2)
    | sP0_iProver_split
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_463])).

cnf(c_569,plain,
    ( k1_relat_1(sK2) = u1_struct_0(sK0)
    | v1_relat_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_321,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_322,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_465,plain,
    ( ~ v1_relat_1(X0_47)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_322])).

cnf(c_568,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0_47)
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_624,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_568])).

cnf(c_625,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_624])).

cnf(c_467,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_48))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_463])).

cnf(c_570,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_48))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_646,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_570])).

cnf(c_647,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_646])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_466,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_657,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_667,plain,
    ( k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_468,c_625,c_647,c_657])).

cnf(c_672,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(X0_47)
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_667,c_568])).

cnf(c_658,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_730,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_672,c_624,c_658])).

cnf(c_9,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_275,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_301,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != u1_struct_0(sK0) ),
    inference(resolution_lifted,[status(thm)],[c_275,c_12])).

cnf(c_348,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(resolution_lifted,[status(thm)],[c_301,c_10])).

cnf(c_464,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(subtyping,[status(esa)],[c_348])).

cnf(c_673,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | u1_struct_0(sK1) != k1_relat_1(sK2)
    | k2_funct_1(sK2) != sK2 ),
    inference(demodulation,[status(thm)],[c_667,c_464])).

cnf(c_567,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:55:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 0.73/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.73/1.02  
% 0.73/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.73/1.02  
% 0.73/1.02  ------  iProver source info
% 0.73/1.02  
% 0.73/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.73/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.73/1.02  git: non_committed_changes: false
% 0.73/1.02  git: last_make_outside_of_git: false
% 0.73/1.02  
% 0.73/1.02  ------ 
% 0.73/1.02  
% 0.73/1.02  ------ Input Options
% 0.73/1.02  
% 0.73/1.02  --out_options                           all
% 0.73/1.02  --tptp_safe_out                         true
% 0.73/1.02  --problem_path                          ""
% 0.73/1.02  --include_path                          ""
% 0.73/1.02  --clausifier                            res/vclausify_rel
% 0.73/1.02  --clausifier_options                    --mode clausify
% 0.73/1.02  --stdin                                 false
% 0.73/1.02  --stats_out                             all
% 0.73/1.02  
% 0.73/1.02  ------ General Options
% 0.73/1.02  
% 0.73/1.02  --fof                                   false
% 0.73/1.02  --time_out_real                         305.
% 0.73/1.02  --time_out_virtual                      -1.
% 0.73/1.02  --symbol_type_check                     false
% 0.73/1.02  --clausify_out                          false
% 0.73/1.02  --sig_cnt_out                           false
% 0.73/1.02  --trig_cnt_out                          false
% 0.73/1.02  --trig_cnt_out_tolerance                1.
% 0.73/1.02  --trig_cnt_out_sk_spl                   false
% 0.73/1.02  --abstr_cl_out                          false
% 0.73/1.02  
% 0.73/1.02  ------ Global Options
% 0.73/1.02  
% 0.73/1.02  --schedule                              default
% 0.73/1.02  --add_important_lit                     false
% 0.73/1.02  --prop_solver_per_cl                    1000
% 0.73/1.02  --min_unsat_core                        false
% 0.73/1.02  --soft_assumptions                      false
% 0.73/1.02  --soft_lemma_size                       3
% 0.73/1.02  --prop_impl_unit_size                   0
% 0.73/1.02  --prop_impl_unit                        []
% 0.73/1.02  --share_sel_clauses                     true
% 0.73/1.02  --reset_solvers                         false
% 0.73/1.02  --bc_imp_inh                            [conj_cone]
% 0.73/1.02  --conj_cone_tolerance                   3.
% 0.73/1.02  --extra_neg_conj                        none
% 0.73/1.02  --large_theory_mode                     true
% 0.73/1.02  --prolific_symb_bound                   200
% 0.73/1.02  --lt_threshold                          2000
% 0.73/1.02  --clause_weak_htbl                      true
% 0.73/1.02  --gc_record_bc_elim                     false
% 0.73/1.02  
% 0.73/1.02  ------ Preprocessing Options
% 0.73/1.02  
% 0.73/1.02  --preprocessing_flag                    true
% 0.73/1.02  --time_out_prep_mult                    0.1
% 0.73/1.02  --splitting_mode                        input
% 0.73/1.02  --splitting_grd                         true
% 0.73/1.02  --splitting_cvd                         false
% 0.73/1.02  --splitting_cvd_svl                     false
% 0.73/1.02  --splitting_nvd                         32
% 0.73/1.02  --sub_typing                            true
% 0.73/1.02  --prep_gs_sim                           true
% 0.73/1.02  --prep_unflatten                        true
% 0.73/1.02  --prep_res_sim                          true
% 0.73/1.02  --prep_upred                            true
% 0.73/1.02  --prep_sem_filter                       exhaustive
% 0.73/1.02  --prep_sem_filter_out                   false
% 0.73/1.02  --pred_elim                             true
% 0.73/1.02  --res_sim_input                         true
% 0.73/1.02  --eq_ax_congr_red                       true
% 0.73/1.02  --pure_diseq_elim                       true
% 0.73/1.02  --brand_transform                       false
% 0.73/1.02  --non_eq_to_eq                          false
% 0.73/1.02  --prep_def_merge                        true
% 0.73/1.02  --prep_def_merge_prop_impl              false
% 0.73/1.02  --prep_def_merge_mbd                    true
% 0.73/1.02  --prep_def_merge_tr_red                 false
% 0.73/1.02  --prep_def_merge_tr_cl                  false
% 0.73/1.02  --smt_preprocessing                     true
% 0.73/1.02  --smt_ac_axioms                         fast
% 0.73/1.02  --preprocessed_out                      false
% 0.73/1.02  --preprocessed_stats                    false
% 0.73/1.02  
% 0.73/1.02  ------ Abstraction refinement Options
% 0.73/1.02  
% 0.73/1.02  --abstr_ref                             []
% 0.73/1.02  --abstr_ref_prep                        false
% 0.73/1.02  --abstr_ref_until_sat                   false
% 0.73/1.02  --abstr_ref_sig_restrict                funpre
% 0.73/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.73/1.02  --abstr_ref_under                       []
% 0.73/1.02  
% 0.73/1.02  ------ SAT Options
% 0.73/1.02  
% 0.73/1.02  --sat_mode                              false
% 0.73/1.02  --sat_fm_restart_options                ""
% 0.73/1.02  --sat_gr_def                            false
% 0.73/1.02  --sat_epr_types                         true
% 0.73/1.02  --sat_non_cyclic_types                  false
% 0.73/1.02  --sat_finite_models                     false
% 0.73/1.02  --sat_fm_lemmas                         false
% 0.73/1.02  --sat_fm_prep                           false
% 0.73/1.02  --sat_fm_uc_incr                        true
% 0.73/1.02  --sat_out_model                         small
% 0.73/1.02  --sat_out_clauses                       false
% 0.73/1.02  
% 0.73/1.02  ------ QBF Options
% 0.73/1.02  
% 0.73/1.02  --qbf_mode                              false
% 0.73/1.02  --qbf_elim_univ                         false
% 0.73/1.02  --qbf_dom_inst                          none
% 0.73/1.02  --qbf_dom_pre_inst                      false
% 0.73/1.02  --qbf_sk_in                             false
% 0.73/1.02  --qbf_pred_elim                         true
% 0.73/1.02  --qbf_split                             512
% 0.73/1.02  
% 0.73/1.02  ------ BMC1 Options
% 0.73/1.02  
% 0.73/1.02  --bmc1_incremental                      false
% 0.73/1.02  --bmc1_axioms                           reachable_all
% 0.73/1.02  --bmc1_min_bound                        0
% 0.73/1.02  --bmc1_max_bound                        -1
% 0.73/1.02  --bmc1_max_bound_default                -1
% 0.73/1.02  --bmc1_symbol_reachability              true
% 0.73/1.02  --bmc1_property_lemmas                  false
% 0.73/1.02  --bmc1_k_induction                      false
% 0.73/1.02  --bmc1_non_equiv_states                 false
% 0.73/1.02  --bmc1_deadlock                         false
% 0.73/1.02  --bmc1_ucm                              false
% 0.73/1.02  --bmc1_add_unsat_core                   none
% 0.73/1.02  --bmc1_unsat_core_children              false
% 0.73/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.73/1.02  --bmc1_out_stat                         full
% 0.73/1.02  --bmc1_ground_init                      false
% 0.73/1.02  --bmc1_pre_inst_next_state              false
% 0.73/1.02  --bmc1_pre_inst_state                   false
% 0.73/1.02  --bmc1_pre_inst_reach_state             false
% 0.73/1.02  --bmc1_out_unsat_core                   false
% 0.73/1.02  --bmc1_aig_witness_out                  false
% 0.73/1.02  --bmc1_verbose                          false
% 0.73/1.02  --bmc1_dump_clauses_tptp                false
% 0.73/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.73/1.02  --bmc1_dump_file                        -
% 0.73/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.73/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.73/1.02  --bmc1_ucm_extend_mode                  1
% 0.73/1.02  --bmc1_ucm_init_mode                    2
% 0.73/1.02  --bmc1_ucm_cone_mode                    none
% 0.73/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.73/1.02  --bmc1_ucm_relax_model                  4
% 0.73/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.73/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.73/1.02  --bmc1_ucm_layered_model                none
% 0.73/1.02  --bmc1_ucm_max_lemma_size               10
% 0.73/1.02  
% 0.73/1.02  ------ AIG Options
% 0.73/1.02  
% 0.73/1.02  --aig_mode                              false
% 0.73/1.02  
% 0.73/1.02  ------ Instantiation Options
% 0.73/1.02  
% 0.73/1.02  --instantiation_flag                    true
% 0.73/1.02  --inst_sos_flag                         false
% 0.73/1.02  --inst_sos_phase                        true
% 0.73/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.73/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.73/1.02  --inst_lit_sel_side                     num_symb
% 0.73/1.02  --inst_solver_per_active                1400
% 0.73/1.02  --inst_solver_calls_frac                1.
% 0.73/1.02  --inst_passive_queue_type               priority_queues
% 0.73/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.73/1.02  --inst_passive_queues_freq              [25;2]
% 0.73/1.02  --inst_dismatching                      true
% 0.73/1.02  --inst_eager_unprocessed_to_passive     true
% 0.73/1.02  --inst_prop_sim_given                   true
% 0.73/1.02  --inst_prop_sim_new                     false
% 0.73/1.02  --inst_subs_new                         false
% 0.73/1.02  --inst_eq_res_simp                      false
% 0.73/1.02  --inst_subs_given                       false
% 0.73/1.02  --inst_orphan_elimination               true
% 0.73/1.02  --inst_learning_loop_flag               true
% 0.73/1.02  --inst_learning_start                   3000
% 0.73/1.02  --inst_learning_factor                  2
% 0.73/1.02  --inst_start_prop_sim_after_learn       3
% 0.73/1.02  --inst_sel_renew                        solver
% 0.73/1.02  --inst_lit_activity_flag                true
% 0.73/1.02  --inst_restr_to_given                   false
% 0.73/1.02  --inst_activity_threshold               500
% 0.73/1.02  --inst_out_proof                        true
% 0.73/1.02  
% 0.73/1.02  ------ Resolution Options
% 0.73/1.02  
% 0.73/1.02  --resolution_flag                       true
% 0.73/1.02  --res_lit_sel                           adaptive
% 0.73/1.02  --res_lit_sel_side                      none
% 0.73/1.02  --res_ordering                          kbo
% 0.73/1.02  --res_to_prop_solver                    active
% 0.73/1.02  --res_prop_simpl_new                    false
% 0.73/1.02  --res_prop_simpl_given                  true
% 0.73/1.02  --res_passive_queue_type                priority_queues
% 0.73/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.73/1.02  --res_passive_queues_freq               [15;5]
% 0.73/1.02  --res_forward_subs                      full
% 0.73/1.02  --res_backward_subs                     full
% 0.73/1.02  --res_forward_subs_resolution           true
% 0.73/1.02  --res_backward_subs_resolution          true
% 0.73/1.02  --res_orphan_elimination                true
% 0.73/1.02  --res_time_limit                        2.
% 0.73/1.02  --res_out_proof                         true
% 0.73/1.02  
% 0.73/1.02  ------ Superposition Options
% 0.73/1.02  
% 0.73/1.02  --superposition_flag                    true
% 0.73/1.02  --sup_passive_queue_type                priority_queues
% 0.73/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.73/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.73/1.02  --demod_completeness_check              fast
% 0.73/1.02  --demod_use_ground                      true
% 0.73/1.02  --sup_to_prop_solver                    passive
% 0.73/1.02  --sup_prop_simpl_new                    true
% 0.73/1.02  --sup_prop_simpl_given                  true
% 0.73/1.02  --sup_fun_splitting                     false
% 0.73/1.02  --sup_smt_interval                      50000
% 0.73/1.02  
% 0.73/1.02  ------ Superposition Simplification Setup
% 0.73/1.02  
% 0.73/1.02  --sup_indices_passive                   []
% 0.73/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.73/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.02  --sup_full_bw                           [BwDemod]
% 0.73/1.02  --sup_immed_triv                        [TrivRules]
% 0.73/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.73/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.02  --sup_immed_bw_main                     []
% 0.73/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.73/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.73/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.73/1.02  
% 0.73/1.02  ------ Combination Options
% 0.73/1.02  
% 0.73/1.02  --comb_res_mult                         3
% 0.73/1.02  --comb_sup_mult                         2
% 0.73/1.02  --comb_inst_mult                        10
% 0.73/1.02  
% 0.73/1.02  ------ Debug Options
% 0.73/1.02  
% 0.73/1.02  --dbg_backtrace                         false
% 0.73/1.02  --dbg_dump_prop_clauses                 false
% 0.73/1.02  --dbg_dump_prop_clauses_file            -
% 0.73/1.02  --dbg_out_stat                          false
% 0.73/1.02  ------ Parsing...
% 0.73/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.73/1.02  
% 0.73/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 0.73/1.02  
% 0.73/1.02  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.73/1.02  
% 0.73/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.73/1.02  ------ Proving...
% 0.73/1.02  ------ Problem Properties 
% 0.73/1.02  
% 0.73/1.02  
% 0.73/1.02  clauses                                 5
% 0.73/1.02  conjectures                             0
% 0.73/1.02  EPR                                     0
% 0.73/1.02  Horn                                    4
% 0.73/1.02  unary                                   1
% 0.73/1.02  binary                                  1
% 0.73/1.02  lits                                    13
% 0.73/1.02  lits eq                                 7
% 0.73/1.02  fd_pure                                 0
% 0.73/1.02  fd_pseudo                               0
% 0.73/1.02  fd_cond                                 0
% 0.73/1.02  fd_pseudo_cond                          0
% 0.73/1.02  AC symbols                              0
% 0.73/1.02  
% 0.73/1.02  ------ Schedule dynamic 5 is on 
% 0.73/1.02  
% 0.73/1.02  ------ no conjectures: strip conj schedule 
% 0.73/1.02  
% 0.73/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 0.73/1.02  
% 0.73/1.02  
% 0.73/1.02  ------ 
% 0.73/1.02  Current options:
% 0.73/1.02  ------ 
% 0.73/1.02  
% 0.73/1.02  ------ Input Options
% 0.73/1.02  
% 0.73/1.02  --out_options                           all
% 0.73/1.02  --tptp_safe_out                         true
% 0.73/1.02  --problem_path                          ""
% 0.73/1.02  --include_path                          ""
% 0.73/1.02  --clausifier                            res/vclausify_rel
% 0.73/1.02  --clausifier_options                    --mode clausify
% 0.73/1.02  --stdin                                 false
% 0.73/1.02  --stats_out                             all
% 0.73/1.02  
% 0.73/1.02  ------ General Options
% 0.73/1.02  
% 0.73/1.02  --fof                                   false
% 0.73/1.02  --time_out_real                         305.
% 0.73/1.02  --time_out_virtual                      -1.
% 0.73/1.02  --symbol_type_check                     false
% 0.73/1.02  --clausify_out                          false
% 0.73/1.02  --sig_cnt_out                           false
% 0.73/1.02  --trig_cnt_out                          false
% 0.73/1.02  --trig_cnt_out_tolerance                1.
% 0.73/1.02  --trig_cnt_out_sk_spl                   false
% 0.73/1.02  --abstr_cl_out                          false
% 0.73/1.02  
% 0.73/1.02  ------ Global Options
% 0.73/1.02  
% 0.73/1.02  --schedule                              default
% 0.73/1.02  --add_important_lit                     false
% 0.73/1.02  --prop_solver_per_cl                    1000
% 0.73/1.02  --min_unsat_core                        false
% 0.73/1.02  --soft_assumptions                      false
% 0.73/1.02  --soft_lemma_size                       3
% 0.73/1.02  --prop_impl_unit_size                   0
% 0.73/1.02  --prop_impl_unit                        []
% 0.73/1.02  --share_sel_clauses                     true
% 0.73/1.02  --reset_solvers                         false
% 0.73/1.02  --bc_imp_inh                            [conj_cone]
% 0.73/1.02  --conj_cone_tolerance                   3.
% 0.73/1.02  --extra_neg_conj                        none
% 0.73/1.02  --large_theory_mode                     true
% 0.73/1.02  --prolific_symb_bound                   200
% 0.73/1.02  --lt_threshold                          2000
% 0.73/1.02  --clause_weak_htbl                      true
% 0.73/1.02  --gc_record_bc_elim                     false
% 0.73/1.02  
% 0.73/1.02  ------ Preprocessing Options
% 0.73/1.02  
% 0.73/1.02  --preprocessing_flag                    true
% 0.73/1.02  --time_out_prep_mult                    0.1
% 0.73/1.02  --splitting_mode                        input
% 0.73/1.02  --splitting_grd                         true
% 0.73/1.02  --splitting_cvd                         false
% 0.73/1.02  --splitting_cvd_svl                     false
% 0.73/1.02  --splitting_nvd                         32
% 0.73/1.02  --sub_typing                            true
% 0.73/1.02  --prep_gs_sim                           true
% 0.73/1.02  --prep_unflatten                        true
% 0.73/1.02  --prep_res_sim                          true
% 0.73/1.02  --prep_upred                            true
% 0.73/1.02  --prep_sem_filter                       exhaustive
% 0.73/1.02  --prep_sem_filter_out                   false
% 0.73/1.02  --pred_elim                             true
% 0.73/1.02  --res_sim_input                         true
% 0.73/1.02  --eq_ax_congr_red                       true
% 0.73/1.02  --pure_diseq_elim                       true
% 0.73/1.02  --brand_transform                       false
% 0.73/1.02  --non_eq_to_eq                          false
% 0.73/1.02  --prep_def_merge                        true
% 0.73/1.02  --prep_def_merge_prop_impl              false
% 0.73/1.02  --prep_def_merge_mbd                    true
% 0.73/1.02  --prep_def_merge_tr_red                 false
% 0.73/1.02  --prep_def_merge_tr_cl                  false
% 0.73/1.02  --smt_preprocessing                     true
% 0.73/1.02  --smt_ac_axioms                         fast
% 0.73/1.02  --preprocessed_out                      false
% 0.73/1.02  --preprocessed_stats                    false
% 0.73/1.02  
% 0.73/1.02  ------ Abstraction refinement Options
% 0.73/1.02  
% 0.73/1.02  --abstr_ref                             []
% 0.73/1.02  --abstr_ref_prep                        false
% 0.73/1.02  --abstr_ref_until_sat                   false
% 0.73/1.02  --abstr_ref_sig_restrict                funpre
% 0.73/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.73/1.02  --abstr_ref_under                       []
% 0.73/1.02  
% 0.73/1.02  ------ SAT Options
% 0.73/1.02  
% 0.73/1.02  --sat_mode                              false
% 0.73/1.02  --sat_fm_restart_options                ""
% 0.73/1.02  --sat_gr_def                            false
% 0.73/1.02  --sat_epr_types                         true
% 0.73/1.02  --sat_non_cyclic_types                  false
% 0.73/1.02  --sat_finite_models                     false
% 0.73/1.02  --sat_fm_lemmas                         false
% 0.73/1.02  --sat_fm_prep                           false
% 0.73/1.02  --sat_fm_uc_incr                        true
% 0.73/1.02  --sat_out_model                         small
% 0.73/1.02  --sat_out_clauses                       false
% 0.73/1.02  
% 0.73/1.02  ------ QBF Options
% 0.73/1.02  
% 0.73/1.02  --qbf_mode                              false
% 0.73/1.02  --qbf_elim_univ                         false
% 0.73/1.02  --qbf_dom_inst                          none
% 0.73/1.02  --qbf_dom_pre_inst                      false
% 0.73/1.02  --qbf_sk_in                             false
% 0.73/1.02  --qbf_pred_elim                         true
% 0.73/1.02  --qbf_split                             512
% 0.73/1.02  
% 0.73/1.02  ------ BMC1 Options
% 0.73/1.02  
% 0.73/1.02  --bmc1_incremental                      false
% 0.73/1.02  --bmc1_axioms                           reachable_all
% 0.73/1.02  --bmc1_min_bound                        0
% 0.73/1.02  --bmc1_max_bound                        -1
% 0.73/1.02  --bmc1_max_bound_default                -1
% 0.73/1.02  --bmc1_symbol_reachability              true
% 0.73/1.02  --bmc1_property_lemmas                  false
% 0.73/1.02  --bmc1_k_induction                      false
% 0.73/1.02  --bmc1_non_equiv_states                 false
% 0.73/1.02  --bmc1_deadlock                         false
% 0.73/1.02  --bmc1_ucm                              false
% 0.73/1.02  --bmc1_add_unsat_core                   none
% 0.73/1.02  --bmc1_unsat_core_children              false
% 0.73/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.73/1.02  --bmc1_out_stat                         full
% 0.73/1.02  --bmc1_ground_init                      false
% 0.73/1.02  --bmc1_pre_inst_next_state              false
% 0.73/1.02  --bmc1_pre_inst_state                   false
% 0.73/1.02  --bmc1_pre_inst_reach_state             false
% 0.73/1.02  --bmc1_out_unsat_core                   false
% 0.73/1.02  --bmc1_aig_witness_out                  false
% 0.73/1.02  --bmc1_verbose                          false
% 0.73/1.02  --bmc1_dump_clauses_tptp                false
% 0.73/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.73/1.02  --bmc1_dump_file                        -
% 0.73/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.73/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.73/1.02  --bmc1_ucm_extend_mode                  1
% 0.73/1.02  --bmc1_ucm_init_mode                    2
% 0.73/1.02  --bmc1_ucm_cone_mode                    none
% 0.73/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.73/1.02  --bmc1_ucm_relax_model                  4
% 0.73/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.73/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.73/1.02  --bmc1_ucm_layered_model                none
% 0.73/1.02  --bmc1_ucm_max_lemma_size               10
% 0.73/1.02  
% 0.73/1.02  ------ AIG Options
% 0.73/1.02  
% 0.73/1.02  --aig_mode                              false
% 0.73/1.02  
% 0.73/1.02  ------ Instantiation Options
% 0.73/1.02  
% 0.73/1.02  --instantiation_flag                    true
% 0.73/1.02  --inst_sos_flag                         false
% 0.73/1.02  --inst_sos_phase                        true
% 0.73/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.73/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.73/1.02  --inst_lit_sel_side                     none
% 0.73/1.02  --inst_solver_per_active                1400
% 0.73/1.02  --inst_solver_calls_frac                1.
% 0.73/1.02  --inst_passive_queue_type               priority_queues
% 0.73/1.02  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 0.73/1.02  --inst_passive_queues_freq              [25;2]
% 0.73/1.02  --inst_dismatching                      true
% 0.73/1.02  --inst_eager_unprocessed_to_passive     true
% 0.73/1.02  --inst_prop_sim_given                   true
% 0.73/1.02  --inst_prop_sim_new                     false
% 0.73/1.02  --inst_subs_new                         false
% 0.73/1.02  --inst_eq_res_simp                      false
% 0.73/1.02  --inst_subs_given                       false
% 0.73/1.02  --inst_orphan_elimination               true
% 0.73/1.02  --inst_learning_loop_flag               true
% 0.73/1.02  --inst_learning_start                   3000
% 0.73/1.02  --inst_learning_factor                  2
% 0.73/1.02  --inst_start_prop_sim_after_learn       3
% 0.73/1.02  --inst_sel_renew                        solver
% 0.73/1.02  --inst_lit_activity_flag                true
% 0.73/1.02  --inst_restr_to_given                   false
% 0.73/1.02  --inst_activity_threshold               500
% 0.73/1.02  --inst_out_proof                        true
% 0.73/1.02  
% 0.73/1.02  ------ Resolution Options
% 0.73/1.02  
% 0.73/1.02  --resolution_flag                       false
% 0.73/1.02  --res_lit_sel                           adaptive
% 0.73/1.02  --res_lit_sel_side                      none
% 0.73/1.02  --res_ordering                          kbo
% 0.73/1.02  --res_to_prop_solver                    active
% 0.73/1.02  --res_prop_simpl_new                    false
% 0.73/1.02  --res_prop_simpl_given                  true
% 0.73/1.02  --res_passive_queue_type                priority_queues
% 0.73/1.02  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 0.73/1.02  --res_passive_queues_freq               [15;5]
% 0.73/1.02  --res_forward_subs                      full
% 0.73/1.02  --res_backward_subs                     full
% 0.73/1.02  --res_forward_subs_resolution           true
% 0.73/1.02  --res_backward_subs_resolution          true
% 0.73/1.02  --res_orphan_elimination                true
% 0.73/1.02  --res_time_limit                        2.
% 0.73/1.02  --res_out_proof                         true
% 0.73/1.02  
% 0.73/1.02  ------ Superposition Options
% 0.73/1.02  
% 0.73/1.02  --superposition_flag                    true
% 0.73/1.02  --sup_passive_queue_type                priority_queues
% 0.73/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.73/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.73/1.02  --demod_completeness_check              fast
% 0.73/1.02  --demod_use_ground                      true
% 0.73/1.02  --sup_to_prop_solver                    passive
% 0.73/1.02  --sup_prop_simpl_new                    true
% 0.73/1.02  --sup_prop_simpl_given                  true
% 0.73/1.02  --sup_fun_splitting                     false
% 0.73/1.02  --sup_smt_interval                      50000
% 0.73/1.02  
% 0.73/1.02  ------ Superposition Simplification Setup
% 0.73/1.02  
% 0.73/1.02  --sup_indices_passive                   []
% 0.73/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.73/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.02  --sup_full_bw                           [BwDemod]
% 0.73/1.02  --sup_immed_triv                        [TrivRules]
% 0.73/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.73/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.02  --sup_immed_bw_main                     []
% 0.73/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.73/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.73/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.73/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.73/1.02  
% 0.73/1.02  ------ Combination Options
% 0.73/1.02  
% 0.73/1.02  --comb_res_mult                         3
% 0.73/1.02  --comb_sup_mult                         2
% 0.73/1.02  --comb_inst_mult                        10
% 0.73/1.02  
% 0.73/1.02  ------ Debug Options
% 0.73/1.02  
% 0.73/1.02  --dbg_backtrace                         false
% 0.73/1.02  --dbg_dump_prop_clauses                 false
% 0.73/1.02  --dbg_dump_prop_clauses_file            -
% 0.73/1.02  --dbg_out_stat                          false
% 0.73/1.02  
% 0.73/1.02  
% 0.73/1.02  
% 0.73/1.02  
% 0.73/1.02  ------ Proving...
% 0.73/1.02  
% 0.73/1.02  
% 0.73/1.02  % SZS status CounterSatisfiable for theBenchmark.p
% 0.73/1.02  
% 0.73/1.02  % SZS output start Saturation for theBenchmark.p
% 0.73/1.02  
% 0.73/1.02  fof(f5,axiom,(
% 0.73/1.02    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.02  
% 0.73/1.02  fof(f16,plain,(
% 0.73/1.02    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.73/1.02    inference(ennf_transformation,[],[f5])).
% 0.73/1.02  
% 0.73/1.02  fof(f17,plain,(
% 0.73/1.02    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.73/1.02    inference(flattening,[],[f16])).
% 0.73/1.02  
% 0.73/1.02  fof(f34,plain,(
% 0.73/1.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.73/1.02    inference(cnf_transformation,[],[f17])).
% 0.73/1.02  
% 0.73/1.02  fof(f9,conjecture,(
% 0.73/1.02    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 0.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.02  
% 0.73/1.02  fof(f10,negated_conjecture,(
% 0.73/1.02    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 0.73/1.02    inference(negated_conjecture,[],[f9])).
% 0.73/1.02  
% 0.73/1.02  fof(f11,plain,(
% 0.73/1.02    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 0.73/1.02    inference(pure_predicate_removal,[],[f10])).
% 0.73/1.02  
% 0.73/1.02  fof(f23,plain,(
% 0.73/1.02    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_orders_2(X1) & ~v2_struct_0(X1))) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.73/1.02    inference(ennf_transformation,[],[f11])).
% 0.73/1.02  
% 0.73/1.02  fof(f24,plain,(
% 0.73/1.02    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 0.73/1.02    inference(flattening,[],[f23])).
% 0.73/1.02  
% 0.73/1.02  fof(f28,plain,(
% 0.73/1.02    ( ! [X0,X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 0.73/1.02    introduced(choice_axiom,[])).
% 0.73/1.02  
% 0.73/1.02  fof(f27,plain,(
% 0.73/1.02    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1))) )),
% 0.73/1.02    introduced(choice_axiom,[])).
% 0.73/1.02  
% 0.73/1.02  fof(f26,plain,(
% 0.73/1.02    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.73/1.02    introduced(choice_axiom,[])).
% 0.73/1.02  
% 0.73/1.02  fof(f29,plain,(
% 0.73/1.02    (((k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.73/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f28,f27,f26])).
% 0.73/1.02  
% 0.73/1.02  fof(f44,plain,(
% 0.73/1.02    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.73/1.02    inference(cnf_transformation,[],[f29])).
% 0.73/1.02  
% 0.73/1.02  fof(f41,plain,(
% 0.73/1.02    ~v2_struct_0(sK1)),
% 0.73/1.02    inference(cnf_transformation,[],[f29])).
% 0.73/1.02  
% 0.73/1.02  fof(f43,plain,(
% 0.73/1.02    v1_funct_1(sK2)),
% 0.73/1.02    inference(cnf_transformation,[],[f29])).
% 0.73/1.02  
% 0.73/1.02  fof(f45,plain,(
% 0.73/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.73/1.02    inference(cnf_transformation,[],[f29])).
% 0.73/1.02  
% 0.73/1.02  fof(f7,axiom,(
% 0.73/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.02  
% 0.73/1.02  fof(f20,plain,(
% 0.73/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.73/1.02    inference(ennf_transformation,[],[f7])).
% 0.73/1.02  
% 0.73/1.02  fof(f21,plain,(
% 0.73/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.73/1.02    inference(flattening,[],[f20])).
% 0.73/1.02  
% 0.73/1.02  fof(f37,plain,(
% 0.73/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.73/1.02    inference(cnf_transformation,[],[f21])).
% 0.73/1.02  
% 0.73/1.02  fof(f8,axiom,(
% 0.73/1.02    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.02  
% 0.73/1.02  fof(f22,plain,(
% 0.73/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.73/1.02    inference(ennf_transformation,[],[f8])).
% 0.73/1.02  
% 0.73/1.02  fof(f38,plain,(
% 0.73/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.73/1.02    inference(cnf_transformation,[],[f22])).
% 0.73/1.02  
% 0.73/1.02  fof(f42,plain,(
% 0.73/1.02    l1_orders_2(sK1)),
% 0.73/1.02    inference(cnf_transformation,[],[f29])).
% 0.73/1.02  
% 0.73/1.02  fof(f6,axiom,(
% 0.73/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.02  
% 0.73/1.02  fof(f18,plain,(
% 0.73/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.73/1.02    inference(ennf_transformation,[],[f6])).
% 0.73/1.02  
% 0.73/1.02  fof(f19,plain,(
% 0.73/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.73/1.02    inference(flattening,[],[f18])).
% 0.73/1.02  
% 0.73/1.02  fof(f25,plain,(
% 0.73/1.02    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.73/1.02    inference(nnf_transformation,[],[f19])).
% 0.73/1.02  
% 0.73/1.02  fof(f35,plain,(
% 0.73/1.02    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.73/1.02    inference(cnf_transformation,[],[f25])).
% 0.73/1.02  
% 0.73/1.02  fof(f4,axiom,(
% 0.73/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.02  
% 0.73/1.02  fof(f12,plain,(
% 0.73/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.73/1.02    inference(pure_predicate_removal,[],[f4])).
% 0.73/1.02  
% 0.73/1.02  fof(f15,plain,(
% 0.73/1.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.73/1.02    inference(ennf_transformation,[],[f12])).
% 0.73/1.02  
% 0.73/1.02  fof(f32,plain,(
% 0.73/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.73/1.02    inference(cnf_transformation,[],[f15])).
% 0.73/1.02  
% 0.73/1.02  fof(f1,axiom,(
% 0.73/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.02  
% 0.73/1.02  fof(f14,plain,(
% 0.73/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.73/1.02    inference(ennf_transformation,[],[f1])).
% 0.73/1.02  
% 0.73/1.02  fof(f30,plain,(
% 0.73/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.73/1.02    inference(cnf_transformation,[],[f14])).
% 0.73/1.02  
% 0.73/1.02  fof(f2,axiom,(
% 0.73/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.02  
% 0.73/1.02  fof(f31,plain,(
% 0.73/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.73/1.02    inference(cnf_transformation,[],[f2])).
% 0.73/1.02  
% 0.73/1.02  fof(f46,plain,(
% 0.73/1.02    k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.73/1.02    inference(cnf_transformation,[],[f29])).
% 0.73/1.02  
% 0.73/1.02  cnf(c_162,plain,
% 0.73/1.02      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 0.73/1.02      theory(equality) ).
% 0.73/1.02  
% 0.73/1.02  cnf(c_161,plain,
% 0.73/1.02      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 0.73/1.02      theory(equality) ).
% 0.73/1.02  
% 0.73/1.02  cnf(c_159,plain,
% 0.73/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 0.73/1.02      theory(equality) ).
% 0.73/1.02  
% 0.73/1.02  cnf(c_158,plain,
% 0.73/1.02      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 0.73/1.02      theory(equality) ).
% 0.73/1.02  
% 0.73/1.02  cnf(c_157,plain,
% 0.73/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 0.73/1.02      | v1_funct_2(X3,X4,X5)
% 0.73/1.02      | X3 != X0
% 0.73/1.02      | X4 != X1
% 0.73/1.02      | X5 != X2 ),
% 0.73/1.02      theory(equality) ).
% 0.73/1.02  
% 0.73/1.02  cnf(c_156,plain,
% 0.73/1.02      ( ~ v1_partfun1(X0,X1) | v1_partfun1(X0,X2) | X2 != X1 ),
% 0.73/1.02      theory(equality) ).
% 0.73/1.02  
% 0.73/1.02  cnf(c_155,plain,
% 0.73/1.02      ( ~ v4_relat_1(X0,X1) | v4_relat_1(X0,X2) | X2 != X1 ),
% 0.73/1.02      theory(equality) ).
% 0.73/1.02  
% 0.73/1.02  cnf(c_153,plain,
% 0.73/1.02      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 0.73/1.02      theory(equality) ).
% 0.73/1.02  
% 0.73/1.02  cnf(c_469,plain,( X0_2 = X0_2 ),theory(equality) ).
% 0.73/1.02  
% 0.73/1.02  cnf(c_3,plain,
% 0.73/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 0.73/1.02      | v1_partfun1(X0,X1)
% 0.73/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.73/1.02      | v1_xboole_0(X2)
% 0.73/1.02      | ~ v1_funct_1(X0) ),
% 0.73/1.02      inference(cnf_transformation,[],[f34]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_11,negated_conjecture,
% 0.73/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 0.73/1.03      inference(cnf_transformation,[],[f44]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_264,plain,
% 0.73/1.03      ( v1_partfun1(X0,X1)
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.73/1.03      | v1_xboole_0(X2)
% 0.73/1.03      | ~ v1_funct_1(X0)
% 0.73/1.03      | u1_struct_0(sK1) != X2
% 0.73/1.03      | u1_struct_0(sK0) != X1
% 0.73/1.03      | sK2 != X0 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_11]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_265,plain,
% 0.73/1.03      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 0.73/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 0.73/1.03      | v1_xboole_0(u1_struct_0(sK1))
% 0.73/1.03      | ~ v1_funct_1(sK2) ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_264]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_14,negated_conjecture,
% 0.73/1.03      ( ~ v2_struct_0(sK1) ),
% 0.73/1.03      inference(cnf_transformation,[],[f41]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_12,negated_conjecture,
% 0.73/1.03      ( v1_funct_1(sK2) ),
% 0.73/1.03      inference(cnf_transformation,[],[f43]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_10,negated_conjecture,
% 0.73/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 0.73/1.03      inference(cnf_transformation,[],[f45]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_7,plain,
% 0.73/1.03      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 0.73/1.03      inference(cnf_transformation,[],[f37]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_8,plain,
% 0.73/1.03      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 0.73/1.03      inference(cnf_transformation,[],[f38]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_13,negated_conjecture,
% 0.73/1.03      ( l1_orders_2(sK1) ),
% 0.73/1.03      inference(cnf_transformation,[],[f42]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_181,plain,
% 0.73/1.03      ( l1_struct_0(X0) | sK1 != X0 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_182,plain,
% 0.73/1.03      ( l1_struct_0(sK1) ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_181]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_210,plain,
% 0.73/1.03      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_182]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_211,plain,
% 0.73/1.03      ( v2_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_210]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_267,plain,
% 0.73/1.03      ( v1_partfun1(sK2,u1_struct_0(sK0)) ),
% 0.73/1.03      inference(global_propositional_subsumption,
% 0.73/1.03                [status(thm)],
% 0.73/1.03                [c_265,c_14,c_12,c_10,c_211]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_6,plain,
% 0.73/1.03      ( ~ v1_partfun1(X0,X1)
% 0.73/1.03      | ~ v4_relat_1(X0,X1)
% 0.73/1.03      | ~ v1_relat_1(X0)
% 0.73/1.03      | k1_relat_1(X0) = X1 ),
% 0.73/1.03      inference(cnf_transformation,[],[f35]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_2,plain,
% 0.73/1.03      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.73/1.03      inference(cnf_transformation,[],[f32]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_336,plain,
% 0.73/1.03      ( v4_relat_1(X0,X1)
% 0.73/1.03      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 0.73/1.03      | sK2 != X0 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_337,plain,
% 0.73/1.03      ( v4_relat_1(sK2,X0)
% 0.73/1.03      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_336]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_372,plain,
% 0.73/1.03      ( ~ v1_partfun1(X0,X1)
% 0.73/1.03      | ~ v1_relat_1(X0)
% 0.73/1.03      | X2 != X1
% 0.73/1.03      | k1_relat_1(X0) = X1
% 0.73/1.03      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 0.73/1.03      | sK2 != X0 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_337]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_373,plain,
% 0.73/1.03      ( ~ v1_partfun1(sK2,X0)
% 0.73/1.03      | ~ v1_relat_1(sK2)
% 0.73/1.03      | k1_relat_1(sK2) = X0
% 0.73/1.03      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_372]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_414,plain,
% 0.73/1.03      ( ~ v1_relat_1(sK2)
% 0.73/1.03      | u1_struct_0(sK0) != X0
% 0.73/1.03      | k1_relat_1(sK2) = X0
% 0.73/1.03      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.73/1.03      | sK2 != sK2 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_267,c_373]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_415,plain,
% 0.73/1.03      ( ~ v1_relat_1(sK2)
% 0.73/1.03      | k1_relat_1(sK2) = u1_struct_0(sK0)
% 0.73/1.03      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)) ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_414]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_463,plain,
% 0.73/1.03      ( ~ v1_relat_1(sK2)
% 0.73/1.03      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_48))
% 0.73/1.03      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 0.73/1.03      inference(subtyping,[status(esa)],[c_415]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_468,plain,
% 0.73/1.03      ( ~ v1_relat_1(sK2)
% 0.73/1.03      | sP0_iProver_split
% 0.73/1.03      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 0.73/1.03      inference(splitting,
% 0.73/1.03                [splitting(split),new_symbols(definition,[])],
% 0.73/1.03                [c_463]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_569,plain,
% 0.73/1.03      ( k1_relat_1(sK2) = u1_struct_0(sK0)
% 0.73/1.03      | v1_relat_1(sK2) != iProver_top
% 0.73/1.03      | sP0_iProver_split = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_0,plain,
% 0.73/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 0.73/1.03      inference(cnf_transformation,[],[f30]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_321,plain,
% 0.73/1.03      ( ~ v1_relat_1(X0)
% 0.73/1.03      | v1_relat_1(X1)
% 0.73/1.03      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
% 0.73/1.03      | sK2 != X1 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_322,plain,
% 0.73/1.03      ( ~ v1_relat_1(X0)
% 0.73/1.03      | v1_relat_1(sK2)
% 0.73/1.03      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_321]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_465,plain,
% 0.73/1.03      ( ~ v1_relat_1(X0_47)
% 0.73/1.03      | v1_relat_1(sK2)
% 0.73/1.03      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0_47) ),
% 0.73/1.03      inference(subtyping,[status(esa)],[c_322]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_568,plain,
% 0.73/1.03      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0_47)
% 0.73/1.03      | v1_relat_1(X0_47) != iProver_top
% 0.73/1.03      | v1_relat_1(sK2) = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_624,plain,
% 0.73/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 0.73/1.03      | v1_relat_1(sK2) = iProver_top ),
% 0.73/1.03      inference(equality_resolution,[status(thm)],[c_568]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_625,plain,
% 0.73/1.03      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 0.73/1.03      | v1_relat_1(sK2) ),
% 0.73/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_624]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_467,plain,
% 0.73/1.03      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_48))
% 0.73/1.03      | ~ sP0_iProver_split ),
% 0.73/1.03      inference(splitting,
% 0.73/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.73/1.03                [c_463]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_570,plain,
% 0.73/1.03      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_48))
% 0.73/1.03      | sP0_iProver_split != iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_646,plain,
% 0.73/1.03      ( sP0_iProver_split != iProver_top ),
% 0.73/1.03      inference(equality_resolution,[status(thm)],[c_570]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_647,plain,
% 0.73/1.03      ( ~ sP0_iProver_split ),
% 0.73/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_646]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1,plain,
% 0.73/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 0.73/1.03      inference(cnf_transformation,[],[f31]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_466,plain,
% 0.73/1.03      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 0.73/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_657,plain,
% 0.73/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 0.73/1.03      inference(instantiation,[status(thm)],[c_466]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_667,plain,
% 0.73/1.03      ( k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 0.73/1.03      inference(global_propositional_subsumption,
% 0.73/1.03                [status(thm)],
% 0.73/1.03                [c_569,c_468,c_625,c_647,c_657]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_672,plain,
% 0.73/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(X0_47)
% 0.73/1.03      | v1_relat_1(X0_47) != iProver_top
% 0.73/1.03      | v1_relat_1(sK2) = iProver_top ),
% 0.73/1.03      inference(demodulation,[status(thm)],[c_667,c_568]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_658,plain,
% 0.73/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_730,plain,
% 0.73/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 0.73/1.03      inference(global_propositional_subsumption,
% 0.73/1.03                [status(thm)],
% 0.73/1.03                [c_672,c_624,c_658]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_9,negated_conjecture,
% 0.73/1.03      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 0.73/1.03      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 0.73/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 0.73/1.03      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 0.73/1.03      inference(cnf_transformation,[],[f46]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_275,plain,
% 0.73/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 0.73/1.03      | ~ v1_funct_1(k2_funct_1(sK2))
% 0.73/1.03      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.73/1.03      | k2_funct_1(sK2) != sK2
% 0.73/1.03      | u1_struct_0(sK1) != u1_struct_0(sK0) ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_301,plain,
% 0.73/1.03      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 0.73/1.03      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.73/1.03      | k2_funct_1(sK2) != sK2
% 0.73/1.03      | u1_struct_0(sK1) != u1_struct_0(sK0) ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_275,c_12]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_348,plain,
% 0.73/1.03      ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.73/1.03      | k2_funct_1(sK2) != sK2
% 0.73/1.03      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 0.73/1.03      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_301,c_10]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_464,plain,
% 0.73/1.03      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 0.73/1.03      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 0.73/1.03      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 0.73/1.03      | k2_funct_1(sK2) != sK2 ),
% 0.73/1.03      inference(subtyping,[status(esa)],[c_348]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_673,plain,
% 0.73/1.03      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
% 0.73/1.03      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 0.73/1.03      | u1_struct_0(sK1) != k1_relat_1(sK2)
% 0.73/1.03      | k2_funct_1(sK2) != sK2 ),
% 0.73/1.03      inference(demodulation,[status(thm)],[c_667,c_464]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_567,plain,
% 0.73/1.03      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 0.73/1.03  
% 0.73/1.03  
% 0.73/1.03  % SZS output end Saturation for theBenchmark.p
% 0.73/1.03  
% 0.73/1.03  ------                               Statistics
% 0.73/1.03  
% 0.73/1.03  ------ General
% 0.73/1.03  
% 0.73/1.03  abstr_ref_over_cycles:                  0
% 0.73/1.03  abstr_ref_under_cycles:                 0
% 0.73/1.03  gc_basic_clause_elim:                   0
% 0.73/1.03  forced_gc_time:                         0
% 0.73/1.03  parsing_time:                           0.007
% 0.73/1.03  unif_index_cands_time:                  0.
% 0.73/1.03  unif_index_add_time:                    0.
% 0.73/1.03  orderings_time:                         0.
% 0.73/1.03  out_proof_time:                         0.
% 0.73/1.03  total_time:                             0.041
% 0.73/1.03  num_of_symbols:                         52
% 0.73/1.03  num_of_terms:                           810
% 0.73/1.03  
% 0.73/1.03  ------ Preprocessing
% 0.73/1.03  
% 0.73/1.03  num_of_splits:                          1
% 0.73/1.03  num_of_split_atoms:                     1
% 0.73/1.03  num_of_reused_defs:                     0
% 0.73/1.03  num_eq_ax_congr_red:                    5
% 0.73/1.03  num_of_sem_filtered_clauses:            1
% 0.73/1.03  num_of_subtypes:                        4
% 0.73/1.03  monotx_restored_types:                  0
% 0.73/1.03  sat_num_of_epr_types:                   0
% 0.73/1.03  sat_num_of_non_cyclic_types:            0
% 0.73/1.03  sat_guarded_non_collapsed_types:        0
% 0.73/1.03  num_pure_diseq_elim:                    0
% 0.73/1.03  simp_replaced_by:                       0
% 0.73/1.03  res_preprocessed:                       55
% 0.73/1.03  prep_upred:                             0
% 0.73/1.03  prep_unflattend:                        17
% 0.73/1.03  smt_new_axioms:                         0
% 0.73/1.03  pred_elim_cands:                        1
% 0.73/1.03  pred_elim:                              9
% 0.73/1.03  pred_elim_cl:                           12
% 0.73/1.03  pred_elim_cycles:                       12
% 0.73/1.03  merged_defs:                            0
% 0.73/1.03  merged_defs_ncl:                        0
% 0.73/1.03  bin_hyper_res:                          0
% 0.73/1.03  prep_cycles:                            4
% 0.73/1.03  pred_elim_time:                         0.003
% 0.73/1.03  splitting_time:                         0.
% 0.73/1.03  sem_filter_time:                        0.
% 0.73/1.03  monotx_time:                            0.
% 0.73/1.03  subtype_inf_time:                       0.
% 0.73/1.03  
% 0.73/1.03  ------ Problem properties
% 0.73/1.03  
% 0.73/1.03  clauses:                                5
% 0.73/1.03  conjectures:                            0
% 0.73/1.03  epr:                                    0
% 0.73/1.03  horn:                                   4
% 0.73/1.03  ground:                                 2
% 0.73/1.03  unary:                                  1
% 0.73/1.03  binary:                                 1
% 0.73/1.03  lits:                                   13
% 0.73/1.03  lits_eq:                                7
% 0.73/1.03  fd_pure:                                0
% 0.73/1.03  fd_pseudo:                              0
% 0.73/1.03  fd_cond:                                0
% 0.73/1.03  fd_pseudo_cond:                         0
% 0.73/1.03  ac_symbols:                             0
% 0.73/1.03  
% 0.73/1.03  ------ Propositional Solver
% 0.73/1.03  
% 0.73/1.03  prop_solver_calls:                      26
% 0.73/1.03  prop_fast_solver_calls:                 324
% 0.73/1.03  smt_solver_calls:                       0
% 0.73/1.03  smt_fast_solver_calls:                  0
% 0.73/1.03  prop_num_of_clauses:                    201
% 0.73/1.03  prop_preprocess_simplified:             1305
% 0.73/1.03  prop_fo_subsumed:                       10
% 0.73/1.03  prop_solver_time:                       0.
% 0.73/1.03  smt_solver_time:                        0.
% 0.73/1.03  smt_fast_solver_time:                   0.
% 0.73/1.03  prop_fast_solver_time:                  0.
% 0.73/1.03  prop_unsat_core_time:                   0.
% 0.73/1.03  
% 0.73/1.03  ------ QBF
% 0.73/1.03  
% 0.73/1.03  qbf_q_res:                              0
% 0.73/1.03  qbf_num_tautologies:                    0
% 0.73/1.03  qbf_prep_cycles:                        0
% 0.73/1.03  
% 0.73/1.03  ------ BMC1
% 0.73/1.03  
% 0.73/1.03  bmc1_current_bound:                     -1
% 0.73/1.03  bmc1_last_solved_bound:                 -1
% 0.73/1.03  bmc1_unsat_core_size:                   -1
% 0.73/1.03  bmc1_unsat_core_parents_size:           -1
% 0.73/1.03  bmc1_merge_next_fun:                    0
% 0.73/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.73/1.03  
% 0.73/1.03  ------ Instantiation
% 0.73/1.03  
% 0.73/1.03  inst_num_of_clauses:                    58
% 0.73/1.03  inst_num_in_passive:                    6
% 0.73/1.03  inst_num_in_active:                     43
% 0.73/1.03  inst_num_in_unprocessed:                9
% 0.73/1.03  inst_num_of_loops:                      50
% 0.73/1.03  inst_num_of_learning_restarts:          0
% 0.73/1.03  inst_num_moves_active_passive:          4
% 0.73/1.03  inst_lit_activity:                      0
% 0.73/1.03  inst_lit_activity_moves:                0
% 0.73/1.03  inst_num_tautologies:                   0
% 0.73/1.03  inst_num_prop_implied:                  0
% 0.73/1.03  inst_num_existing_simplified:           0
% 0.73/1.03  inst_num_eq_res_simplified:             0
% 0.73/1.03  inst_num_child_elim:                    0
% 0.73/1.03  inst_num_of_dismatching_blockings:      3
% 0.73/1.03  inst_num_of_non_proper_insts:           39
% 0.73/1.03  inst_num_of_duplicates:                 0
% 0.73/1.03  inst_inst_num_from_inst_to_res:         0
% 0.73/1.03  inst_dismatching_checking_time:         0.
% 0.73/1.03  
% 0.73/1.03  ------ Resolution
% 0.73/1.03  
% 0.73/1.03  res_num_of_clauses:                     0
% 0.73/1.03  res_num_in_passive:                     0
% 0.73/1.03  res_num_in_active:                      0
% 0.73/1.03  res_num_of_loops:                       59
% 0.73/1.03  res_forward_subset_subsumed:            8
% 0.73/1.03  res_backward_subset_subsumed:           0
% 0.73/1.03  res_forward_subsumed:                   0
% 0.73/1.03  res_backward_subsumed:                  0
% 0.73/1.03  res_forward_subsumption_resolution:     0
% 0.73/1.03  res_backward_subsumption_resolution:    0
% 0.73/1.03  res_clause_to_clause_subsumption:       10
% 0.73/1.03  res_orphan_elimination:                 0
% 0.73/1.03  res_tautology_del:                      8
% 0.73/1.03  res_num_eq_res_simplified:              0
% 0.73/1.03  res_num_sel_changes:                    0
% 0.73/1.03  res_moves_from_active_to_pass:          0
% 0.73/1.03  
% 0.73/1.03  ------ Superposition
% 0.73/1.03  
% 0.73/1.03  sup_time_total:                         0.
% 0.73/1.03  sup_time_generating:                    0.
% 0.73/1.03  sup_time_sim_full:                      0.
% 0.73/1.03  sup_time_sim_immed:                     0.
% 0.73/1.03  
% 0.73/1.03  sup_num_of_clauses:                     5
% 0.73/1.03  sup_num_in_active:                      5
% 0.73/1.03  sup_num_in_passive:                     0
% 0.73/1.03  sup_num_of_loops:                       9
% 0.73/1.03  sup_fw_superposition:                   0
% 0.73/1.03  sup_bw_superposition:                   0
% 0.73/1.03  sup_immediate_simplified:               1
% 0.73/1.03  sup_given_eliminated:                   0
% 0.73/1.03  comparisons_done:                       0
% 0.73/1.03  comparisons_avoided:                    0
% 0.73/1.03  
% 0.73/1.03  ------ Simplifications
% 0.73/1.03  
% 0.73/1.03  
% 0.73/1.03  sim_fw_subset_subsumed:                 1
% 0.73/1.03  sim_bw_subset_subsumed:                 0
% 0.73/1.03  sim_fw_subsumed:                        0
% 0.73/1.03  sim_bw_subsumed:                        0
% 0.73/1.03  sim_fw_subsumption_res:                 0
% 0.73/1.03  sim_bw_subsumption_res:                 0
% 0.73/1.03  sim_tautology_del:                      0
% 0.73/1.03  sim_eq_tautology_del:                   0
% 0.73/1.03  sim_eq_res_simp:                        0
% 0.73/1.03  sim_fw_demodulated:                     0
% 0.73/1.03  sim_bw_demodulated:                     4
% 0.73/1.03  sim_light_normalised:                   0
% 0.73/1.03  sim_joinable_taut:                      0
% 0.73/1.03  sim_joinable_simp:                      0
% 0.73/1.03  sim_ac_normalised:                      0
% 0.73/1.03  sim_smt_subsumption:                    0
% 0.73/1.03  
%------------------------------------------------------------------------------
