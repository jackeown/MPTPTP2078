%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:16 EST 2020

% Result     : CounterSatisfiable 1.39s
% Output     : Saturation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 955 expanded)
%              Number of clauses        :   93 ( 284 expanded)
%              Number of leaves         :   25 ( 261 expanded)
%              Depth                    :   15
%              Number of atoms          :  573 (7535 expanded)
%              Number of equality atoms :  229 (1258 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f13])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f37,f36,f35])).

fof(f67,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_295,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_294,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_292,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_284,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_280,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_696,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_493,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_22])).

cnf(c_16,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_389,plain,
    ( v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) != X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_390,plain,
    ( v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_578,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(X0,X1,sK2) != X0
    | u1_struct_0(sK1) != X0
    | u1_struct_0(sK0) != X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_493,c_390])).

cnf(c_579,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_687,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_579])).

cnf(c_849,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_695,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_726,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_317,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_20,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_342,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_343,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_361,plain,
    ( v2_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_317,c_343])).

cnf(c_362,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_364,plain,
    ( u1_struct_0(sK0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_28])).

cnf(c_691,plain,
    ( u1_struct_0(sK0) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_364])).

cnf(c_699,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_921,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_416,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_417,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_689,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_417])).

cnf(c_923,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_701,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_936,plain,
    ( u1_struct_0(sK0) != X0_49
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != X0_49 ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_961,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_936])).

cnf(c_697,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_962,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_1176,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_849,c_24,c_726,c_691,c_687,c_921,c_923,c_961,c_962])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_407,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_408,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_690,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_408])).

cnf(c_920,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_690])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_371,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_372,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | k1_relset_1(X0,X1,sK2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_602,plain,
    ( k1_relset_1(X0,X1,sK2) = X0
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK0) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_372])).

cnf(c_603,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_686,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_603])).

cnf(c_950,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_920,c_686])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_335,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_336,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_353,plain,
    ( v2_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_317,c_336])).

cnf(c_354,plain,
    ( v2_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_356,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_26])).

cnf(c_692,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_1063,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_950,c_692])).

cnf(c_1178,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | k2_funct_1(sK2) != sK2
    | k1_relset_1(u1_struct_0(sK1),k1_relat_1(sK2),sK2) != u1_struct_0(sK1)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1176,c_1063])).

cnf(c_1069,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1063,c_690])).

cnf(c_1068,plain,
    ( k1_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1063,c_691])).

cnf(c_1067,plain,
    ( k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1063,c_920])).

cnf(c_560,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_493,c_23])).

cnf(c_688,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_560])).

cnf(c_848,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_976,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_funct_1(sK2) != sK2
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_848,c_24,c_726,c_688,c_921,c_923])).

cnf(c_977,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != u1_struct_0(sK0)
    | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_976])).

cnf(c_1066,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | k2_funct_1(sK2) != sK2
    | u1_struct_0(sK1) != k1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1063,c_977])).

cnf(c_847,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_924,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_923])).

cnf(c_970,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_847,c_921,c_924])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_694,plain,
    ( ~ v1_relat_1(X0_50)
    | v1_relat_1(k2_funct_1(X0_50))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_845,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k2_funct_1(X0_50)) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_844,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_693,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_846,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.39/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.39/1.03  
% 1.39/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.39/1.03  
% 1.39/1.03  ------  iProver source info
% 1.39/1.03  
% 1.39/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.39/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.39/1.03  git: non_committed_changes: false
% 1.39/1.03  git: last_make_outside_of_git: false
% 1.39/1.03  
% 1.39/1.03  ------ 
% 1.39/1.03  
% 1.39/1.03  ------ Input Options
% 1.39/1.03  
% 1.39/1.03  --out_options                           all
% 1.39/1.03  --tptp_safe_out                         true
% 1.39/1.03  --problem_path                          ""
% 1.39/1.03  --include_path                          ""
% 1.39/1.03  --clausifier                            res/vclausify_rel
% 1.39/1.03  --clausifier_options                    --mode clausify
% 1.39/1.03  --stdin                                 false
% 1.39/1.03  --stats_out                             all
% 1.39/1.03  
% 1.39/1.03  ------ General Options
% 1.39/1.03  
% 1.39/1.03  --fof                                   false
% 1.39/1.03  --time_out_real                         305.
% 1.39/1.03  --time_out_virtual                      -1.
% 1.39/1.03  --symbol_type_check                     false
% 1.39/1.03  --clausify_out                          false
% 1.39/1.03  --sig_cnt_out                           false
% 1.39/1.03  --trig_cnt_out                          false
% 1.39/1.03  --trig_cnt_out_tolerance                1.
% 1.39/1.03  --trig_cnt_out_sk_spl                   false
% 1.39/1.03  --abstr_cl_out                          false
% 1.39/1.03  
% 1.39/1.03  ------ Global Options
% 1.39/1.03  
% 1.39/1.03  --schedule                              default
% 1.39/1.03  --add_important_lit                     false
% 1.39/1.03  --prop_solver_per_cl                    1000
% 1.39/1.03  --min_unsat_core                        false
% 1.39/1.03  --soft_assumptions                      false
% 1.39/1.03  --soft_lemma_size                       3
% 1.39/1.03  --prop_impl_unit_size                   0
% 1.39/1.03  --prop_impl_unit                        []
% 1.39/1.03  --share_sel_clauses                     true
% 1.39/1.03  --reset_solvers                         false
% 1.39/1.03  --bc_imp_inh                            [conj_cone]
% 1.39/1.03  --conj_cone_tolerance                   3.
% 1.39/1.03  --extra_neg_conj                        none
% 1.39/1.03  --large_theory_mode                     true
% 1.39/1.03  --prolific_symb_bound                   200
% 1.39/1.03  --lt_threshold                          2000
% 1.39/1.03  --clause_weak_htbl                      true
% 1.39/1.03  --gc_record_bc_elim                     false
% 1.39/1.03  
% 1.39/1.03  ------ Preprocessing Options
% 1.39/1.03  
% 1.39/1.03  --preprocessing_flag                    true
% 1.39/1.03  --time_out_prep_mult                    0.1
% 1.39/1.03  --splitting_mode                        input
% 1.39/1.03  --splitting_grd                         true
% 1.39/1.03  --splitting_cvd                         false
% 1.39/1.03  --splitting_cvd_svl                     false
% 1.39/1.03  --splitting_nvd                         32
% 1.39/1.03  --sub_typing                            true
% 1.39/1.03  --prep_gs_sim                           true
% 1.39/1.03  --prep_unflatten                        true
% 1.39/1.03  --prep_res_sim                          true
% 1.39/1.03  --prep_upred                            true
% 1.39/1.03  --prep_sem_filter                       exhaustive
% 1.39/1.03  --prep_sem_filter_out                   false
% 1.39/1.03  --pred_elim                             true
% 1.39/1.03  --res_sim_input                         true
% 1.39/1.03  --eq_ax_congr_red                       true
% 1.39/1.03  --pure_diseq_elim                       true
% 1.39/1.03  --brand_transform                       false
% 1.39/1.03  --non_eq_to_eq                          false
% 1.39/1.03  --prep_def_merge                        true
% 1.39/1.03  --prep_def_merge_prop_impl              false
% 1.39/1.03  --prep_def_merge_mbd                    true
% 1.39/1.03  --prep_def_merge_tr_red                 false
% 1.39/1.03  --prep_def_merge_tr_cl                  false
% 1.39/1.03  --smt_preprocessing                     true
% 1.39/1.03  --smt_ac_axioms                         fast
% 1.39/1.03  --preprocessed_out                      false
% 1.39/1.03  --preprocessed_stats                    false
% 1.39/1.03  
% 1.39/1.03  ------ Abstraction refinement Options
% 1.39/1.03  
% 1.39/1.03  --abstr_ref                             []
% 1.39/1.03  --abstr_ref_prep                        false
% 1.39/1.03  --abstr_ref_until_sat                   false
% 1.39/1.03  --abstr_ref_sig_restrict                funpre
% 1.39/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.39/1.03  --abstr_ref_under                       []
% 1.39/1.03  
% 1.39/1.03  ------ SAT Options
% 1.39/1.03  
% 1.39/1.03  --sat_mode                              false
% 1.39/1.03  --sat_fm_restart_options                ""
% 1.39/1.03  --sat_gr_def                            false
% 1.39/1.03  --sat_epr_types                         true
% 1.39/1.03  --sat_non_cyclic_types                  false
% 1.39/1.03  --sat_finite_models                     false
% 1.39/1.03  --sat_fm_lemmas                         false
% 1.39/1.03  --sat_fm_prep                           false
% 1.39/1.03  --sat_fm_uc_incr                        true
% 1.39/1.03  --sat_out_model                         small
% 1.39/1.03  --sat_out_clauses                       false
% 1.39/1.03  
% 1.39/1.03  ------ QBF Options
% 1.39/1.03  
% 1.39/1.03  --qbf_mode                              false
% 1.39/1.03  --qbf_elim_univ                         false
% 1.39/1.03  --qbf_dom_inst                          none
% 1.39/1.03  --qbf_dom_pre_inst                      false
% 1.39/1.03  --qbf_sk_in                             false
% 1.39/1.03  --qbf_pred_elim                         true
% 1.39/1.03  --qbf_split                             512
% 1.39/1.03  
% 1.39/1.03  ------ BMC1 Options
% 1.39/1.03  
% 1.39/1.03  --bmc1_incremental                      false
% 1.39/1.03  --bmc1_axioms                           reachable_all
% 1.39/1.03  --bmc1_min_bound                        0
% 1.39/1.03  --bmc1_max_bound                        -1
% 1.39/1.03  --bmc1_max_bound_default                -1
% 1.39/1.03  --bmc1_symbol_reachability              true
% 1.39/1.03  --bmc1_property_lemmas                  false
% 1.39/1.03  --bmc1_k_induction                      false
% 1.39/1.03  --bmc1_non_equiv_states                 false
% 1.39/1.03  --bmc1_deadlock                         false
% 1.39/1.03  --bmc1_ucm                              false
% 1.39/1.03  --bmc1_add_unsat_core                   none
% 1.39/1.03  --bmc1_unsat_core_children              false
% 1.39/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.39/1.03  --bmc1_out_stat                         full
% 1.39/1.03  --bmc1_ground_init                      false
% 1.39/1.03  --bmc1_pre_inst_next_state              false
% 1.39/1.03  --bmc1_pre_inst_state                   false
% 1.39/1.03  --bmc1_pre_inst_reach_state             false
% 1.39/1.03  --bmc1_out_unsat_core                   false
% 1.39/1.03  --bmc1_aig_witness_out                  false
% 1.39/1.03  --bmc1_verbose                          false
% 1.39/1.03  --bmc1_dump_clauses_tptp                false
% 1.39/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.39/1.03  --bmc1_dump_file                        -
% 1.39/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.39/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.39/1.03  --bmc1_ucm_extend_mode                  1
% 1.39/1.03  --bmc1_ucm_init_mode                    2
% 1.39/1.03  --bmc1_ucm_cone_mode                    none
% 1.39/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.39/1.03  --bmc1_ucm_relax_model                  4
% 1.39/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.39/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.39/1.03  --bmc1_ucm_layered_model                none
% 1.39/1.03  --bmc1_ucm_max_lemma_size               10
% 1.39/1.03  
% 1.39/1.03  ------ AIG Options
% 1.39/1.03  
% 1.39/1.03  --aig_mode                              false
% 1.39/1.03  
% 1.39/1.03  ------ Instantiation Options
% 1.39/1.03  
% 1.39/1.03  --instantiation_flag                    true
% 1.39/1.03  --inst_sos_flag                         false
% 1.39/1.03  --inst_sos_phase                        true
% 1.39/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.39/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.39/1.03  --inst_lit_sel_side                     num_symb
% 1.39/1.03  --inst_solver_per_active                1400
% 1.39/1.03  --inst_solver_calls_frac                1.
% 1.39/1.03  --inst_passive_queue_type               priority_queues
% 1.39/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.39/1.03  --inst_passive_queues_freq              [25;2]
% 1.39/1.03  --inst_dismatching                      true
% 1.39/1.03  --inst_eager_unprocessed_to_passive     true
% 1.39/1.03  --inst_prop_sim_given                   true
% 1.39/1.03  --inst_prop_sim_new                     false
% 1.39/1.03  --inst_subs_new                         false
% 1.39/1.03  --inst_eq_res_simp                      false
% 1.39/1.03  --inst_subs_given                       false
% 1.39/1.03  --inst_orphan_elimination               true
% 1.39/1.03  --inst_learning_loop_flag               true
% 1.39/1.03  --inst_learning_start                   3000
% 1.39/1.03  --inst_learning_factor                  2
% 1.39/1.03  --inst_start_prop_sim_after_learn       3
% 1.39/1.03  --inst_sel_renew                        solver
% 1.39/1.03  --inst_lit_activity_flag                true
% 1.39/1.03  --inst_restr_to_given                   false
% 1.39/1.03  --inst_activity_threshold               500
% 1.39/1.03  --inst_out_proof                        true
% 1.39/1.03  
% 1.39/1.03  ------ Resolution Options
% 1.39/1.03  
% 1.39/1.03  --resolution_flag                       true
% 1.39/1.03  --res_lit_sel                           adaptive
% 1.39/1.03  --res_lit_sel_side                      none
% 1.39/1.03  --res_ordering                          kbo
% 1.39/1.03  --res_to_prop_solver                    active
% 1.39/1.03  --res_prop_simpl_new                    false
% 1.39/1.03  --res_prop_simpl_given                  true
% 1.39/1.03  --res_passive_queue_type                priority_queues
% 1.39/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.39/1.03  --res_passive_queues_freq               [15;5]
% 1.39/1.03  --res_forward_subs                      full
% 1.39/1.03  --res_backward_subs                     full
% 1.39/1.03  --res_forward_subs_resolution           true
% 1.39/1.03  --res_backward_subs_resolution          true
% 1.39/1.03  --res_orphan_elimination                true
% 1.39/1.03  --res_time_limit                        2.
% 1.39/1.03  --res_out_proof                         true
% 1.39/1.03  
% 1.39/1.03  ------ Superposition Options
% 1.39/1.03  
% 1.39/1.03  --superposition_flag                    true
% 1.39/1.03  --sup_passive_queue_type                priority_queues
% 1.39/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.39/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.39/1.03  --demod_completeness_check              fast
% 1.39/1.03  --demod_use_ground                      true
% 1.39/1.03  --sup_to_prop_solver                    passive
% 1.39/1.03  --sup_prop_simpl_new                    true
% 1.39/1.03  --sup_prop_simpl_given                  true
% 1.39/1.03  --sup_fun_splitting                     false
% 1.39/1.03  --sup_smt_interval                      50000
% 1.39/1.03  
% 1.39/1.03  ------ Superposition Simplification Setup
% 1.39/1.03  
% 1.39/1.03  --sup_indices_passive                   []
% 1.39/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.39/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.03  --sup_full_bw                           [BwDemod]
% 1.39/1.03  --sup_immed_triv                        [TrivRules]
% 1.39/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.39/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.03  --sup_immed_bw_main                     []
% 1.39/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.39/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/1.03  
% 1.39/1.03  ------ Combination Options
% 1.39/1.03  
% 1.39/1.03  --comb_res_mult                         3
% 1.39/1.03  --comb_sup_mult                         2
% 1.39/1.03  --comb_inst_mult                        10
% 1.39/1.03  
% 1.39/1.03  ------ Debug Options
% 1.39/1.03  
% 1.39/1.03  --dbg_backtrace                         false
% 1.39/1.03  --dbg_dump_prop_clauses                 false
% 1.39/1.03  --dbg_dump_prop_clauses_file            -
% 1.39/1.03  --dbg_out_stat                          false
% 1.39/1.03  ------ Parsing...
% 1.39/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.39/1.03  
% 1.39/1.03  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.39/1.03  
% 1.39/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.39/1.03  
% 1.39/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.39/1.03  ------ Proving...
% 1.39/1.03  ------ Problem Properties 
% 1.39/1.03  
% 1.39/1.03  
% 1.39/1.03  clauses                                 10
% 1.39/1.03  conjectures                             1
% 1.39/1.03  EPR                                     1
% 1.39/1.03  Horn                                    9
% 1.39/1.03  unary                                   3
% 1.39/1.03  binary                                  3
% 1.39/1.03  lits                                    26
% 1.39/1.03  lits eq                                 16
% 1.39/1.03  fd_pure                                 0
% 1.39/1.03  fd_pseudo                               0
% 1.39/1.03  fd_cond                                 0
% 1.39/1.03  fd_pseudo_cond                          0
% 1.39/1.03  AC symbols                              0
% 1.39/1.03  
% 1.39/1.03  ------ Schedule dynamic 5 is on 
% 1.39/1.03  
% 1.39/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.39/1.03  
% 1.39/1.03  
% 1.39/1.03  ------ 
% 1.39/1.03  Current options:
% 1.39/1.03  ------ 
% 1.39/1.03  
% 1.39/1.03  ------ Input Options
% 1.39/1.03  
% 1.39/1.03  --out_options                           all
% 1.39/1.03  --tptp_safe_out                         true
% 1.39/1.03  --problem_path                          ""
% 1.39/1.03  --include_path                          ""
% 1.39/1.03  --clausifier                            res/vclausify_rel
% 1.39/1.03  --clausifier_options                    --mode clausify
% 1.39/1.03  --stdin                                 false
% 1.39/1.03  --stats_out                             all
% 1.39/1.03  
% 1.39/1.03  ------ General Options
% 1.39/1.03  
% 1.39/1.03  --fof                                   false
% 1.39/1.03  --time_out_real                         305.
% 1.39/1.03  --time_out_virtual                      -1.
% 1.39/1.03  --symbol_type_check                     false
% 1.39/1.03  --clausify_out                          false
% 1.39/1.03  --sig_cnt_out                           false
% 1.39/1.03  --trig_cnt_out                          false
% 1.39/1.03  --trig_cnt_out_tolerance                1.
% 1.39/1.03  --trig_cnt_out_sk_spl                   false
% 1.39/1.03  --abstr_cl_out                          false
% 1.39/1.03  
% 1.39/1.03  ------ Global Options
% 1.39/1.03  
% 1.39/1.03  --schedule                              default
% 1.39/1.03  --add_important_lit                     false
% 1.39/1.03  --prop_solver_per_cl                    1000
% 1.39/1.03  --min_unsat_core                        false
% 1.39/1.03  --soft_assumptions                      false
% 1.39/1.03  --soft_lemma_size                       3
% 1.39/1.03  --prop_impl_unit_size                   0
% 1.39/1.03  --prop_impl_unit                        []
% 1.39/1.03  --share_sel_clauses                     true
% 1.39/1.03  --reset_solvers                         false
% 1.39/1.03  --bc_imp_inh                            [conj_cone]
% 1.39/1.03  --conj_cone_tolerance                   3.
% 1.39/1.03  --extra_neg_conj                        none
% 1.39/1.03  --large_theory_mode                     true
% 1.39/1.03  --prolific_symb_bound                   200
% 1.39/1.03  --lt_threshold                          2000
% 1.39/1.03  --clause_weak_htbl                      true
% 1.39/1.03  --gc_record_bc_elim                     false
% 1.39/1.03  
% 1.39/1.03  ------ Preprocessing Options
% 1.39/1.03  
% 1.39/1.03  --preprocessing_flag                    true
% 1.39/1.03  --time_out_prep_mult                    0.1
% 1.39/1.03  --splitting_mode                        input
% 1.39/1.03  --splitting_grd                         true
% 1.39/1.03  --splitting_cvd                         false
% 1.39/1.03  --splitting_cvd_svl                     false
% 1.39/1.03  --splitting_nvd                         32
% 1.39/1.03  --sub_typing                            true
% 1.39/1.03  --prep_gs_sim                           true
% 1.39/1.03  --prep_unflatten                        true
% 1.39/1.03  --prep_res_sim                          true
% 1.39/1.03  --prep_upred                            true
% 1.39/1.03  --prep_sem_filter                       exhaustive
% 1.39/1.03  --prep_sem_filter_out                   false
% 1.39/1.03  --pred_elim                             true
% 1.39/1.03  --res_sim_input                         true
% 1.39/1.03  --eq_ax_congr_red                       true
% 1.39/1.03  --pure_diseq_elim                       true
% 1.39/1.03  --brand_transform                       false
% 1.39/1.03  --non_eq_to_eq                          false
% 1.39/1.03  --prep_def_merge                        true
% 1.39/1.03  --prep_def_merge_prop_impl              false
% 1.39/1.03  --prep_def_merge_mbd                    true
% 1.39/1.03  --prep_def_merge_tr_red                 false
% 1.39/1.03  --prep_def_merge_tr_cl                  false
% 1.39/1.03  --smt_preprocessing                     true
% 1.39/1.03  --smt_ac_axioms                         fast
% 1.39/1.03  --preprocessed_out                      false
% 1.39/1.03  --preprocessed_stats                    false
% 1.39/1.03  
% 1.39/1.03  ------ Abstraction refinement Options
% 1.39/1.03  
% 1.39/1.03  --abstr_ref                             []
% 1.39/1.03  --abstr_ref_prep                        false
% 1.39/1.03  --abstr_ref_until_sat                   false
% 1.39/1.03  --abstr_ref_sig_restrict                funpre
% 1.39/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.39/1.03  --abstr_ref_under                       []
% 1.39/1.03  
% 1.39/1.03  ------ SAT Options
% 1.39/1.03  
% 1.39/1.03  --sat_mode                              false
% 1.39/1.03  --sat_fm_restart_options                ""
% 1.39/1.03  --sat_gr_def                            false
% 1.39/1.03  --sat_epr_types                         true
% 1.39/1.03  --sat_non_cyclic_types                  false
% 1.39/1.03  --sat_finite_models                     false
% 1.39/1.03  --sat_fm_lemmas                         false
% 1.39/1.03  --sat_fm_prep                           false
% 1.39/1.03  --sat_fm_uc_incr                        true
% 1.39/1.03  --sat_out_model                         small
% 1.39/1.03  --sat_out_clauses                       false
% 1.39/1.03  
% 1.39/1.03  ------ QBF Options
% 1.39/1.03  
% 1.39/1.03  --qbf_mode                              false
% 1.39/1.03  --qbf_elim_univ                         false
% 1.39/1.03  --qbf_dom_inst                          none
% 1.39/1.03  --qbf_dom_pre_inst                      false
% 1.39/1.03  --qbf_sk_in                             false
% 1.39/1.03  --qbf_pred_elim                         true
% 1.39/1.03  --qbf_split                             512
% 1.39/1.03  
% 1.39/1.03  ------ BMC1 Options
% 1.39/1.03  
% 1.39/1.03  --bmc1_incremental                      false
% 1.39/1.03  --bmc1_axioms                           reachable_all
% 1.39/1.03  --bmc1_min_bound                        0
% 1.39/1.03  --bmc1_max_bound                        -1
% 1.39/1.03  --bmc1_max_bound_default                -1
% 1.39/1.03  --bmc1_symbol_reachability              true
% 1.39/1.03  --bmc1_property_lemmas                  false
% 1.39/1.03  --bmc1_k_induction                      false
% 1.39/1.03  --bmc1_non_equiv_states                 false
% 1.39/1.03  --bmc1_deadlock                         false
% 1.39/1.03  --bmc1_ucm                              false
% 1.39/1.03  --bmc1_add_unsat_core                   none
% 1.39/1.03  --bmc1_unsat_core_children              false
% 1.39/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.39/1.03  --bmc1_out_stat                         full
% 1.39/1.03  --bmc1_ground_init                      false
% 1.39/1.03  --bmc1_pre_inst_next_state              false
% 1.39/1.03  --bmc1_pre_inst_state                   false
% 1.39/1.03  --bmc1_pre_inst_reach_state             false
% 1.39/1.03  --bmc1_out_unsat_core                   false
% 1.39/1.03  --bmc1_aig_witness_out                  false
% 1.39/1.03  --bmc1_verbose                          false
% 1.39/1.03  --bmc1_dump_clauses_tptp                false
% 1.39/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.39/1.03  --bmc1_dump_file                        -
% 1.39/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.39/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.39/1.03  --bmc1_ucm_extend_mode                  1
% 1.39/1.03  --bmc1_ucm_init_mode                    2
% 1.39/1.03  --bmc1_ucm_cone_mode                    none
% 1.39/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.39/1.03  --bmc1_ucm_relax_model                  4
% 1.39/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.39/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.39/1.03  --bmc1_ucm_layered_model                none
% 1.39/1.03  --bmc1_ucm_max_lemma_size               10
% 1.39/1.03  
% 1.39/1.03  ------ AIG Options
% 1.39/1.03  
% 1.39/1.03  --aig_mode                              false
% 1.39/1.03  
% 1.39/1.03  ------ Instantiation Options
% 1.39/1.03  
% 1.39/1.03  --instantiation_flag                    true
% 1.39/1.03  --inst_sos_flag                         false
% 1.39/1.03  --inst_sos_phase                        true
% 1.39/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.39/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.39/1.03  --inst_lit_sel_side                     none
% 1.39/1.03  --inst_solver_per_active                1400
% 1.39/1.03  --inst_solver_calls_frac                1.
% 1.39/1.03  --inst_passive_queue_type               priority_queues
% 1.39/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.39/1.03  --inst_passive_queues_freq              [25;2]
% 1.39/1.03  --inst_dismatching                      true
% 1.39/1.03  --inst_eager_unprocessed_to_passive     true
% 1.39/1.03  --inst_prop_sim_given                   true
% 1.39/1.03  --inst_prop_sim_new                     false
% 1.39/1.03  --inst_subs_new                         false
% 1.39/1.03  --inst_eq_res_simp                      false
% 1.39/1.03  --inst_subs_given                       false
% 1.39/1.03  --inst_orphan_elimination               true
% 1.39/1.03  --inst_learning_loop_flag               true
% 1.39/1.03  --inst_learning_start                   3000
% 1.39/1.03  --inst_learning_factor                  2
% 1.39/1.03  --inst_start_prop_sim_after_learn       3
% 1.39/1.03  --inst_sel_renew                        solver
% 1.39/1.03  --inst_lit_activity_flag                true
% 1.39/1.03  --inst_restr_to_given                   false
% 1.39/1.03  --inst_activity_threshold               500
% 1.39/1.03  --inst_out_proof                        true
% 1.39/1.03  
% 1.39/1.03  ------ Resolution Options
% 1.39/1.03  
% 1.39/1.03  --resolution_flag                       false
% 1.39/1.03  --res_lit_sel                           adaptive
% 1.39/1.03  --res_lit_sel_side                      none
% 1.39/1.03  --res_ordering                          kbo
% 1.39/1.03  --res_to_prop_solver                    active
% 1.39/1.03  --res_prop_simpl_new                    false
% 1.39/1.03  --res_prop_simpl_given                  true
% 1.39/1.03  --res_passive_queue_type                priority_queues
% 1.39/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.39/1.03  --res_passive_queues_freq               [15;5]
% 1.39/1.03  --res_forward_subs                      full
% 1.39/1.03  --res_backward_subs                     full
% 1.39/1.03  --res_forward_subs_resolution           true
% 1.39/1.03  --res_backward_subs_resolution          true
% 1.39/1.03  --res_orphan_elimination                true
% 1.39/1.03  --res_time_limit                        2.
% 1.39/1.03  --res_out_proof                         true
% 1.39/1.03  
% 1.39/1.03  ------ Superposition Options
% 1.39/1.03  
% 1.39/1.03  --superposition_flag                    true
% 1.39/1.03  --sup_passive_queue_type                priority_queues
% 1.39/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.39/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.39/1.03  --demod_completeness_check              fast
% 1.39/1.03  --demod_use_ground                      true
% 1.39/1.03  --sup_to_prop_solver                    passive
% 1.39/1.03  --sup_prop_simpl_new                    true
% 1.39/1.03  --sup_prop_simpl_given                  true
% 1.39/1.03  --sup_fun_splitting                     false
% 1.39/1.03  --sup_smt_interval                      50000
% 1.39/1.03  
% 1.39/1.03  ------ Superposition Simplification Setup
% 1.39/1.03  
% 1.39/1.03  --sup_indices_passive                   []
% 1.39/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.39/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.03  --sup_full_bw                           [BwDemod]
% 1.39/1.03  --sup_immed_triv                        [TrivRules]
% 1.39/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.39/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.03  --sup_immed_bw_main                     []
% 1.39/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.39/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/1.03  
% 1.39/1.03  ------ Combination Options
% 1.39/1.03  
% 1.39/1.03  --comb_res_mult                         3
% 1.39/1.03  --comb_sup_mult                         2
% 1.39/1.03  --comb_inst_mult                        10
% 1.39/1.03  
% 1.39/1.03  ------ Debug Options
% 1.39/1.03  
% 1.39/1.03  --dbg_backtrace                         false
% 1.39/1.03  --dbg_dump_prop_clauses                 false
% 1.39/1.03  --dbg_dump_prop_clauses_file            -
% 1.39/1.03  --dbg_out_stat                          false
% 1.39/1.03  
% 1.39/1.03  
% 1.39/1.03  
% 1.39/1.03  
% 1.39/1.03  ------ Proving...
% 1.39/1.03  
% 1.39/1.03  
% 1.39/1.03  % SZS status CounterSatisfiable for theBenchmark.p
% 1.39/1.03  
% 1.39/1.03  % SZS output start Saturation for theBenchmark.p
% 1.39/1.03  
% 1.39/1.03  fof(f6,axiom,(
% 1.39/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.39/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.03  
% 1.39/1.03  fof(f23,plain,(
% 1.39/1.03    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/1.03    inference(ennf_transformation,[],[f6])).
% 1.39/1.03  
% 1.39/1.03  fof(f24,plain,(
% 1.39/1.03    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/1.03    inference(flattening,[],[f23])).
% 1.39/1.03  
% 1.39/1.03  fof(f49,plain,(
% 1.39/1.03    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/1.03    inference(cnf_transformation,[],[f24])).
% 1.39/1.03  
% 1.39/1.03  fof(f5,axiom,(
% 1.39/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 1.39/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.03  
% 1.39/1.03  fof(f21,plain,(
% 1.39/1.03    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/1.03    inference(ennf_transformation,[],[f5])).
% 1.39/1.03  
% 1.39/1.03  fof(f22,plain,(
% 1.39/1.03    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/1.03    inference(flattening,[],[f21])).
% 1.39/1.03  
% 1.39/1.03  fof(f47,plain,(
% 1.39/1.03    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/1.03    inference(cnf_transformation,[],[f22])).
% 1.39/1.03  
% 1.39/1.03  fof(f48,plain,(
% 1.39/1.03    ( ! [X0] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/1.03    inference(cnf_transformation,[],[f22])).
% 1.39/1.03  
% 1.39/1.03  fof(f4,axiom,(
% 1.39/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.39/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.03  
% 1.39/1.03  fof(f19,plain,(
% 1.39/1.03    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/1.03    inference(ennf_transformation,[],[f4])).
% 1.39/1.03  
% 1.39/1.03  fof(f20,plain,(
% 1.39/1.03    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/1.03    inference(flattening,[],[f19])).
% 1.39/1.03  
% 1.39/1.03  fof(f45,plain,(
% 1.39/1.03    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/1.03    inference(cnf_transformation,[],[f20])).
% 1.39/1.03  
% 1.39/1.03  fof(f46,plain,(
% 1.39/1.03    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/1.03    inference(cnf_transformation,[],[f20])).
% 1.39/1.03  
% 1.39/1.03  fof(f3,axiom,(
% 1.39/1.03    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.39/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.03  
% 1.39/1.03  fof(f17,plain,(
% 1.39/1.03    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/1.03    inference(ennf_transformation,[],[f3])).
% 1.39/1.03  
% 1.39/1.03  fof(f18,plain,(
% 1.39/1.03    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/1.03    inference(flattening,[],[f17])).
% 1.39/1.03  
% 1.39/1.03  fof(f44,plain,(
% 1.39/1.03    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/1.03    inference(cnf_transformation,[],[f18])).
% 1.39/1.03  
% 1.39/1.03  fof(f12,conjecture,(
% 1.39/1.03    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 1.39/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.04  
% 1.39/1.04  fof(f13,negated_conjecture,(
% 1.39/1.04    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 1.39/1.04    inference(negated_conjecture,[],[f12])).
% 1.39/1.04  
% 1.39/1.04  fof(f14,plain,(
% 1.39/1.04    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 1.39/1.04    inference(pure_predicate_removal,[],[f13])).
% 1.39/1.04  
% 1.39/1.04  fof(f32,plain,(
% 1.39/1.04    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_orders_2(X1) & ~v2_struct_0(X1))) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.39/1.04    inference(ennf_transformation,[],[f14])).
% 1.39/1.04  
% 1.39/1.04  fof(f33,plain,(
% 1.39/1.04    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 1.39/1.04    inference(flattening,[],[f32])).
% 1.39/1.04  
% 1.39/1.04  fof(f37,plain,(
% 1.39/1.04    ( ! [X0,X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 1.39/1.04    introduced(choice_axiom,[])).
% 1.39/1.04  
% 1.39/1.04  fof(f36,plain,(
% 1.39/1.04    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1))) )),
% 1.39/1.04    introduced(choice_axiom,[])).
% 1.39/1.04  
% 1.39/1.04  fof(f35,plain,(
% 1.39/1.04    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.39/1.04    introduced(choice_axiom,[])).
% 1.39/1.04  
% 1.39/1.04  fof(f38,plain,(
% 1.39/1.04    (((k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.39/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f37,f36,f35])).
% 1.39/1.04  
% 1.39/1.04  fof(f67,plain,(
% 1.39/1.04    k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.39/1.04    inference(cnf_transformation,[],[f38])).
% 1.39/1.04  
% 1.39/1.04  fof(f66,plain,(
% 1.39/1.04    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.39/1.04    inference(cnf_transformation,[],[f38])).
% 1.39/1.04  
% 1.39/1.04  fof(f9,axiom,(
% 1.39/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.39/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.04  
% 1.39/1.04  fof(f27,plain,(
% 1.39/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/1.04    inference(ennf_transformation,[],[f9])).
% 1.39/1.04  
% 1.39/1.04  fof(f28,plain,(
% 1.39/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/1.04    inference(flattening,[],[f27])).
% 1.39/1.04  
% 1.39/1.04  fof(f34,plain,(
% 1.39/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/1.04    inference(nnf_transformation,[],[f28])).
% 1.39/1.04  
% 1.39/1.04  fof(f54,plain,(
% 1.39/1.04    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/1.04    inference(cnf_transformation,[],[f34])).
% 1.39/1.04  
% 1.39/1.04  fof(f64,plain,(
% 1.39/1.04    v1_funct_1(sK2)),
% 1.39/1.04    inference(cnf_transformation,[],[f38])).
% 1.39/1.04  
% 1.39/1.04  fof(f2,axiom,(
% 1.39/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.39/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.04  
% 1.39/1.04  fof(f15,plain,(
% 1.39/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/1.04    inference(ennf_transformation,[],[f2])).
% 1.39/1.04  
% 1.39/1.04  fof(f16,plain,(
% 1.39/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/1.04    inference(flattening,[],[f15])).
% 1.39/1.04  
% 1.39/1.04  fof(f41,plain,(
% 1.39/1.04    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/1.04    inference(cnf_transformation,[],[f16])).
% 1.39/1.04  
% 1.39/1.04  fof(f1,axiom,(
% 1.39/1.04    v1_xboole_0(k1_xboole_0)),
% 1.39/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.04  
% 1.39/1.04  fof(f39,plain,(
% 1.39/1.04    v1_xboole_0(k1_xboole_0)),
% 1.39/1.04    inference(cnf_transformation,[],[f1])).
% 1.39/1.04  
% 1.39/1.04  fof(f10,axiom,(
% 1.39/1.04    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.39/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.04  
% 1.39/1.04  fof(f29,plain,(
% 1.39/1.04    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.39/1.04    inference(ennf_transformation,[],[f10])).
% 1.39/1.04  
% 1.39/1.04  fof(f30,plain,(
% 1.39/1.04    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.39/1.04    inference(flattening,[],[f29])).
% 1.39/1.04  
% 1.39/1.04  fof(f58,plain,(
% 1.39/1.04    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.39/1.04    inference(cnf_transformation,[],[f30])).
% 1.39/1.04  
% 1.39/1.04  fof(f11,axiom,(
% 1.39/1.04    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.39/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.04  
% 1.39/1.04  fof(f31,plain,(
% 1.39/1.04    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.39/1.04    inference(ennf_transformation,[],[f11])).
% 1.39/1.04  
% 1.39/1.04  fof(f59,plain,(
% 1.39/1.04    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.39/1.04    inference(cnf_transformation,[],[f31])).
% 1.39/1.04  
% 1.39/1.04  fof(f61,plain,(
% 1.39/1.04    l1_orders_2(sK0)),
% 1.39/1.04    inference(cnf_transformation,[],[f38])).
% 1.39/1.04  
% 1.39/1.04  fof(f60,plain,(
% 1.39/1.04    ~v2_struct_0(sK0)),
% 1.39/1.04    inference(cnf_transformation,[],[f38])).
% 1.39/1.04  
% 1.39/1.04  fof(f7,axiom,(
% 1.39/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.39/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.04  
% 1.39/1.04  fof(f25,plain,(
% 1.39/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/1.04    inference(ennf_transformation,[],[f7])).
% 1.39/1.04  
% 1.39/1.04  fof(f50,plain,(
% 1.39/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/1.04    inference(cnf_transformation,[],[f25])).
% 1.39/1.04  
% 1.39/1.04  fof(f8,axiom,(
% 1.39/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.39/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.04  
% 1.39/1.04  fof(f26,plain,(
% 1.39/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/1.04    inference(ennf_transformation,[],[f8])).
% 1.39/1.04  
% 1.39/1.04  fof(f51,plain,(
% 1.39/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/1.04    inference(cnf_transformation,[],[f26])).
% 1.39/1.04  
% 1.39/1.04  fof(f65,plain,(
% 1.39/1.04    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.39/1.04    inference(cnf_transformation,[],[f38])).
% 1.39/1.04  
% 1.39/1.04  fof(f52,plain,(
% 1.39/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/1.04    inference(cnf_transformation,[],[f34])).
% 1.39/1.04  
% 1.39/1.04  fof(f63,plain,(
% 1.39/1.04    l1_orders_2(sK1)),
% 1.39/1.04    inference(cnf_transformation,[],[f38])).
% 1.39/1.04  
% 1.39/1.04  fof(f62,plain,(
% 1.39/1.04    ~v2_struct_0(sK1)),
% 1.39/1.04    inference(cnf_transformation,[],[f38])).
% 1.39/1.04  
% 1.39/1.04  fof(f40,plain,(
% 1.39/1.04    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/1.04    inference(cnf_transformation,[],[f16])).
% 1.39/1.04  
% 1.39/1.04  cnf(c_295,plain,
% 1.39/1.04      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 1.39/1.04      theory(equality) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_294,plain,
% 1.39/1.04      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 1.39/1.04      theory(equality) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_292,plain,
% 1.39/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.39/1.04      | v1_funct_2(X3,X4,X5)
% 1.39/1.04      | X3 != X0
% 1.39/1.04      | X4 != X1
% 1.39/1.04      | X5 != X2 ),
% 1.39/1.04      theory(equality) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_290,plain,
% 1.39/1.04      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.39/1.04      theory(equality) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_284,plain,
% 1.39/1.04      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 1.39/1.04      theory(equality) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_280,plain,
% 1.39/1.04      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.39/1.04      theory(equality) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_696,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_10,plain,
% 1.39/1.04      ( ~ v2_funct_1(X0)
% 1.39/1.04      | ~ v1_relat_1(X0)
% 1.39/1.04      | ~ v1_funct_1(X0)
% 1.39/1.04      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 1.39/1.04      inference(cnf_transformation,[],[f49]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_9,plain,
% 1.39/1.04      ( ~ v2_funct_1(X0)
% 1.39/1.04      | ~ v1_relat_1(X0)
% 1.39/1.04      | ~ v1_funct_1(X0)
% 1.39/1.04      | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f47]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_8,plain,
% 1.39/1.04      ( ~ v2_funct_1(X0)
% 1.39/1.04      | ~ v1_relat_1(X0)
% 1.39/1.04      | ~ v1_funct_1(X0)
% 1.39/1.04      | k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f48]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_7,plain,
% 1.39/1.04      ( ~ v2_funct_1(X0)
% 1.39/1.04      | ~ v1_relat_1(X0)
% 1.39/1.04      | ~ v1_funct_1(X0)
% 1.39/1.04      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f45]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_6,plain,
% 1.39/1.04      ( ~ v2_funct_1(X0)
% 1.39/1.04      | ~ v1_relat_1(X0)
% 1.39/1.04      | ~ v1_funct_1(X0)
% 1.39/1.04      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f46]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_3,plain,
% 1.39/1.04      ( ~ v2_funct_1(X0)
% 1.39/1.04      | v2_funct_1(k2_funct_1(X0))
% 1.39/1.04      | ~ v1_relat_1(X0)
% 1.39/1.04      | ~ v1_funct_1(X0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f44]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_21,negated_conjecture,
% 1.39/1.04      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.39/1.04      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.39/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f67]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_22,negated_conjecture,
% 1.39/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.39/1.04      inference(cnf_transformation,[],[f66]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_493,plain,
% 1.39/1.04      ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.39/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.39/1.04      | k2_funct_1(sK2) != sK2 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_21,c_22]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_16,plain,
% 1.39/1.04      ( v1_funct_2(X0,X1,X2)
% 1.39/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.39/1.04      | k1_relset_1(X1,X2,X0) != X1
% 1.39/1.04      | k1_xboole_0 = X2 ),
% 1.39/1.04      inference(cnf_transformation,[],[f54]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_389,plain,
% 1.39/1.04      ( v1_funct_2(X0,X1,X2)
% 1.39/1.04      | k1_relset_1(X1,X2,X0) != X1
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.39/1.04      | sK2 != X0
% 1.39/1.04      | k1_xboole_0 = X2 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_390,plain,
% 1.39/1.04      ( v1_funct_2(sK2,X0,X1)
% 1.39/1.04      | k1_relset_1(X0,X1,sK2) != X0
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.39/1.04      | k1_xboole_0 = X1 ),
% 1.39/1.04      inference(unflattening,[status(thm)],[c_389]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_578,plain,
% 1.39/1.04      ( ~ v1_funct_1(k2_funct_1(sK2))
% 1.39/1.04      | k1_relset_1(X0,X1,sK2) != X0
% 1.39/1.04      | u1_struct_0(sK1) != X0
% 1.39/1.04      | u1_struct_0(sK0) != X1
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.39/1.04      | k2_funct_1(sK2) != sK2
% 1.39/1.04      | k1_xboole_0 = X1 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_493,c_390]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_579,plain,
% 1.39/1.04      ( ~ v1_funct_1(k2_funct_1(sK2))
% 1.39/1.04      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.39/1.04      | k2_funct_1(sK2) != sK2
% 1.39/1.04      | k1_xboole_0 = u1_struct_0(sK0) ),
% 1.39/1.04      inference(unflattening,[status(thm)],[c_578]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_687,plain,
% 1.39/1.04      ( ~ v1_funct_1(k2_funct_1(sK2))
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.39/1.04      | k2_funct_1(sK2) != sK2
% 1.39/1.04      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.39/1.04      | k1_xboole_0 = u1_struct_0(sK0) ),
% 1.39/1.04      inference(subtyping,[status(esa)],[c_579]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_849,plain,
% 1.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.39/1.04      | k2_funct_1(sK2) != sK2
% 1.39/1.04      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.39/1.04      | k1_xboole_0 = u1_struct_0(sK0)
% 1.39/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.39/1.04      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_24,negated_conjecture,
% 1.39/1.04      ( v1_funct_1(sK2) ),
% 1.39/1.04      inference(cnf_transformation,[],[f64]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_1,plain,
% 1.39/1.04      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 1.39/1.04      inference(cnf_transformation,[],[f41]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_695,plain,
% 1.39/1.04      ( ~ v1_relat_1(X0_50)
% 1.39/1.04      | ~ v1_funct_1(X0_50)
% 1.39/1.04      | v1_funct_1(k2_funct_1(X0_50)) ),
% 1.39/1.04      inference(subtyping,[status(esa)],[c_1]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_726,plain,
% 1.39/1.04      ( ~ v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) ),
% 1.39/1.04      inference(instantiation,[status(thm)],[c_695]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_0,plain,
% 1.39/1.04      ( v1_xboole_0(k1_xboole_0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f39]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_19,plain,
% 1.39/1.04      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.39/1.04      inference(cnf_transformation,[],[f58]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_317,plain,
% 1.39/1.04      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_20,plain,
% 1.39/1.04      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f59]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_27,negated_conjecture,
% 1.39/1.04      ( l1_orders_2(sK0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f61]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_342,plain,
% 1.39/1.04      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_343,plain,
% 1.39/1.04      ( l1_struct_0(sK0) ),
% 1.39/1.04      inference(unflattening,[status(thm)],[c_342]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_361,plain,
% 1.39/1.04      ( v2_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK0 != X0 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_317,c_343]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_362,plain,
% 1.39/1.04      ( v2_struct_0(sK0) | u1_struct_0(sK0) != k1_xboole_0 ),
% 1.39/1.04      inference(unflattening,[status(thm)],[c_361]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_28,negated_conjecture,
% 1.39/1.04      ( ~ v2_struct_0(sK0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f60]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_364,plain,
% 1.39/1.04      ( u1_struct_0(sK0) != k1_xboole_0 ),
% 1.39/1.04      inference(global_propositional_subsumption,[status(thm)],[c_362,c_28]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_691,plain,
% 1.39/1.04      ( u1_struct_0(sK0) != k1_xboole_0 ),
% 1.39/1.04      inference(subtyping,[status(esa)],[c_364]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_699,plain,( X0_52 = X0_52 ),theory(equality) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_921,plain,
% 1.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.39/1.04      inference(instantiation,[status(thm)],[c_699]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_11,plain,
% 1.39/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f50]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_416,plain,
% 1.39/1.04      ( v1_relat_1(X0)
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.39/1.04      | sK2 != X0 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_417,plain,
% 1.39/1.04      ( v1_relat_1(sK2)
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.39/1.04      inference(unflattening,[status(thm)],[c_416]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_689,plain,
% 1.39/1.04      ( v1_relat_1(sK2)
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 1.39/1.04      inference(subtyping,[status(esa)],[c_417]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_923,plain,
% 1.39/1.04      ( v1_relat_1(sK2)
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.39/1.04      inference(instantiation,[status(thm)],[c_689]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_701,plain,
% 1.39/1.04      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 1.39/1.04      theory(equality) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_936,plain,
% 1.39/1.04      ( u1_struct_0(sK0) != X0_49
% 1.39/1.04      | u1_struct_0(sK0) = k1_xboole_0
% 1.39/1.04      | k1_xboole_0 != X0_49 ),
% 1.39/1.04      inference(instantiation,[status(thm)],[c_701]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_961,plain,
% 1.39/1.04      ( u1_struct_0(sK0) != u1_struct_0(sK0)
% 1.39/1.04      | u1_struct_0(sK0) = k1_xboole_0
% 1.39/1.04      | k1_xboole_0 != u1_struct_0(sK0) ),
% 1.39/1.04      inference(instantiation,[status(thm)],[c_936]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_697,plain,( X0_49 = X0_49 ),theory(equality) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_962,plain,
% 1.39/1.04      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 1.39/1.04      inference(instantiation,[status(thm)],[c_697]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_1176,plain,
% 1.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.39/1.04      | k2_funct_1(sK2) != sK2
% 1.39/1.04      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) != u1_struct_0(sK1)
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.39/1.04      inference(global_propositional_subsumption,
% 1.39/1.04                [status(thm)],
% 1.39/1.04                [c_849,c_24,c_726,c_691,c_687,c_921,c_923,c_961,c_962]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_12,plain,
% 1.39/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.39/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f51]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_407,plain,
% 1.39/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.39/1.04      | sK2 != X2 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_408,plain,
% 1.39/1.04      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.39/1.04      inference(unflattening,[status(thm)],[c_407]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_690,plain,
% 1.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 1.39/1.04      | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2) ),
% 1.39/1.04      inference(subtyping,[status(esa)],[c_408]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_920,plain,
% 1.39/1.04      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 1.39/1.04      inference(equality_resolution,[status(thm)],[c_690]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_23,negated_conjecture,
% 1.39/1.04      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.39/1.04      inference(cnf_transformation,[],[f65]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_18,plain,
% 1.39/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.39/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.39/1.04      | k1_relset_1(X1,X2,X0) = X1
% 1.39/1.04      | k1_xboole_0 = X2 ),
% 1.39/1.04      inference(cnf_transformation,[],[f52]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_371,plain,
% 1.39/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.39/1.04      | k1_relset_1(X1,X2,X0) = X1
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.39/1.04      | sK2 != X0
% 1.39/1.04      | k1_xboole_0 = X2 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_372,plain,
% 1.39/1.04      ( ~ v1_funct_2(sK2,X0,X1)
% 1.39/1.04      | k1_relset_1(X0,X1,sK2) = X0
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.39/1.04      | k1_xboole_0 = X1 ),
% 1.39/1.04      inference(unflattening,[status(thm)],[c_371]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_602,plain,
% 1.39/1.04      ( k1_relset_1(X0,X1,sK2) = X0
% 1.39/1.04      | u1_struct_0(sK1) != X1
% 1.39/1.04      | u1_struct_0(sK0) != X0
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.39/1.04      | sK2 != sK2
% 1.39/1.04      | k1_xboole_0 = X1 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_23,c_372]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_603,plain,
% 1.39/1.04      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
% 1.39/1.04      | k1_xboole_0 = u1_struct_0(sK1) ),
% 1.39/1.04      inference(unflattening,[status(thm)],[c_602]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_686,plain,
% 1.39/1.04      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK0)
% 1.39/1.04      | k1_xboole_0 = u1_struct_0(sK1) ),
% 1.39/1.04      inference(subtyping,[status(esa)],[c_603]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_950,plain,
% 1.39/1.04      ( u1_struct_0(sK1) = k1_xboole_0 | u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 1.39/1.04      inference(demodulation,[status(thm)],[c_920,c_686]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_25,negated_conjecture,
% 1.39/1.04      ( l1_orders_2(sK1) ),
% 1.39/1.04      inference(cnf_transformation,[],[f63]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_335,plain,
% 1.39/1.04      ( l1_struct_0(X0) | sK1 != X0 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_336,plain,
% 1.39/1.04      ( l1_struct_0(sK1) ),
% 1.39/1.04      inference(unflattening,[status(thm)],[c_335]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_353,plain,
% 1.39/1.04      ( v2_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_317,c_336]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_354,plain,
% 1.39/1.04      ( v2_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 1.39/1.04      inference(unflattening,[status(thm)],[c_353]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_26,negated_conjecture,
% 1.39/1.04      ( ~ v2_struct_0(sK1) ),
% 1.39/1.04      inference(cnf_transformation,[],[f62]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_356,plain,
% 1.39/1.04      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 1.39/1.04      inference(global_propositional_subsumption,[status(thm)],[c_354,c_26]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_692,plain,
% 1.39/1.04      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 1.39/1.04      inference(subtyping,[status(esa)],[c_356]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_1063,plain,
% 1.39/1.04      ( u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 1.39/1.04      inference(global_propositional_subsumption,[status(thm)],[c_950,c_692]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_1178,plain,
% 1.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
% 1.39/1.04      | k2_funct_1(sK2) != sK2
% 1.39/1.04      | k1_relset_1(u1_struct_0(sK1),k1_relat_1(sK2),sK2) != u1_struct_0(sK1)
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 1.39/1.04      inference(light_normalisation,[status(thm)],[c_1176,c_1063]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_1069,plain,
% 1.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 1.39/1.04      | k1_relset_1(X0_49,X1_49,sK2) = k1_relat_1(sK2) ),
% 1.39/1.04      inference(demodulation,[status(thm)],[c_1063,c_690]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_1068,plain,
% 1.39/1.04      ( k1_relat_1(sK2) != k1_xboole_0 ),
% 1.39/1.04      inference(demodulation,[status(thm)],[c_1063,c_691]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_1067,plain,
% 1.39/1.04      ( k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 1.39/1.04      inference(demodulation,[status(thm)],[c_1063,c_920]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_560,plain,
% 1.39/1.04      ( ~ v1_funct_1(k2_funct_1(sK2))
% 1.39/1.04      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.39/1.04      | k2_funct_1(sK2) != sK2 ),
% 1.39/1.04      inference(resolution_lifted,[status(thm)],[c_493,c_23]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_688,plain,
% 1.39/1.04      ( ~ v1_funct_1(k2_funct_1(sK2))
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.39/1.04      | k2_funct_1(sK2) != sK2
% 1.39/1.04      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.39/1.04      inference(subtyping,[status(esa)],[c_560]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_848,plain,
% 1.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.39/1.04      | k2_funct_1(sK2) != sK2
% 1.39/1.04      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.39/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.39/1.04      inference(predicate_to_equality,[status(thm)],[c_688]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_976,plain,
% 1.39/1.04      ( k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0)
% 1.39/1.04      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 1.39/1.04      | k2_funct_1(sK2) != sK2
% 1.39/1.04      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 1.39/1.04      inference(global_propositional_subsumption,
% 1.39/1.04                [status(thm)],
% 1.39/1.04                [c_848,c_24,c_726,c_688,c_921,c_923]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_977,plain,
% 1.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.39/1.04      | k2_funct_1(sK2) != sK2
% 1.39/1.04      | u1_struct_0(sK1) != u1_struct_0(sK0)
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != u1_struct_0(sK0) ),
% 1.39/1.04      inference(renaming,[status(thm)],[c_976]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_1066,plain,
% 1.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
% 1.39/1.04      | k2_funct_1(sK2) != sK2
% 1.39/1.04      | u1_struct_0(sK1) != k1_relat_1(sK2)
% 1.39/1.04      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 1.39/1.04      inference(demodulation,[status(thm)],[c_1063,c_977]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_847,plain,
% 1.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 1.39/1.04      | v1_relat_1(sK2) = iProver_top ),
% 1.39/1.04      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_924,plain,
% 1.39/1.04      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 1.39/1.04      | v1_relat_1(sK2) = iProver_top ),
% 1.39/1.04      inference(predicate_to_equality,[status(thm)],[c_923]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_970,plain,
% 1.39/1.04      ( v1_relat_1(sK2) = iProver_top ),
% 1.39/1.04      inference(global_propositional_subsumption,
% 1.39/1.04                [status(thm)],
% 1.39/1.04                [c_847,c_921,c_924]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_2,plain,
% 1.39/1.04      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 1.39/1.04      inference(cnf_transformation,[],[f40]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_694,plain,
% 1.39/1.04      ( ~ v1_relat_1(X0_50)
% 1.39/1.04      | v1_relat_1(k2_funct_1(X0_50))
% 1.39/1.04      | ~ v1_funct_1(X0_50) ),
% 1.39/1.04      inference(subtyping,[status(esa)],[c_2]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_845,plain,
% 1.39/1.04      ( v1_relat_1(X0_50) != iProver_top
% 1.39/1.04      | v1_relat_1(k2_funct_1(X0_50)) = iProver_top
% 1.39/1.04      | v1_funct_1(X0_50) != iProver_top ),
% 1.39/1.04      inference(predicate_to_equality,[status(thm)],[c_694]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_844,plain,
% 1.39/1.04      ( v1_relat_1(X0_50) != iProver_top
% 1.39/1.04      | v1_funct_1(X0_50) != iProver_top
% 1.39/1.04      | v1_funct_1(k2_funct_1(X0_50)) = iProver_top ),
% 1.39/1.04      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_693,negated_conjecture,
% 1.39/1.04      ( v1_funct_1(sK2) ),
% 1.39/1.04      inference(subtyping,[status(esa)],[c_24]) ).
% 1.39/1.04  
% 1.39/1.04  cnf(c_846,plain,
% 1.39/1.04      ( v1_funct_1(sK2) = iProver_top ),
% 1.39/1.04      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 1.39/1.04  
% 1.39/1.04  
% 1.39/1.04  % SZS output end Saturation for theBenchmark.p
% 1.39/1.04  
% 1.39/1.04  ------                               Statistics
% 1.39/1.04  
% 1.39/1.04  ------ General
% 1.39/1.04  
% 1.39/1.04  abstr_ref_over_cycles:                  0
% 1.39/1.04  abstr_ref_under_cycles:                 0
% 1.39/1.04  gc_basic_clause_elim:                   0
% 1.39/1.04  forced_gc_time:                         0
% 1.39/1.04  parsing_time:                           0.021
% 1.39/1.04  unif_index_cands_time:                  0.
% 1.39/1.04  unif_index_add_time:                    0.
% 1.39/1.04  orderings_time:                         0.
% 1.39/1.04  out_proof_time:                         0.
% 1.39/1.04  total_time:                             0.09
% 1.39/1.04  num_of_symbols:                         57
% 1.39/1.04  num_of_terms:                           1083
% 1.39/1.04  
% 1.39/1.04  ------ Preprocessing
% 1.39/1.04  
% 1.39/1.04  num_of_splits:                          0
% 1.39/1.04  num_of_split_atoms:                     0
% 1.39/1.04  num_of_reused_defs:                     0
% 1.39/1.04  num_eq_ax_congr_red:                    4
% 1.39/1.04  num_of_sem_filtered_clauses:            7
% 1.39/1.04  num_of_subtypes:                        5
% 1.39/1.04  monotx_restored_types:                  0
% 1.39/1.04  sat_num_of_epr_types:                   0
% 1.39/1.04  sat_num_of_non_cyclic_types:            0
% 1.39/1.04  sat_guarded_non_collapsed_types:        0
% 1.39/1.04  num_pure_diseq_elim:                    0
% 1.39/1.04  simp_replaced_by:                       0
% 1.39/1.04  res_preprocessed:                       88
% 1.39/1.04  prep_upred:                             0
% 1.39/1.04  prep_unflattend:                        32
% 1.39/1.04  smt_new_axioms:                         0
% 1.39/1.04  pred_elim_cands:                        2
% 1.39/1.04  pred_elim:                              6
% 1.39/1.04  pred_elim_cl:                           11
% 1.39/1.04  pred_elim_cycles:                       8
% 1.39/1.04  merged_defs:                            0
% 1.39/1.04  merged_defs_ncl:                        0
% 1.39/1.04  bin_hyper_res:                          0
% 1.39/1.04  prep_cycles:                            4
% 1.39/1.04  pred_elim_time:                         0.007
% 1.39/1.04  splitting_time:                         0.
% 1.39/1.04  sem_filter_time:                        0.
% 1.39/1.04  monotx_time:                            0.
% 1.39/1.04  subtype_inf_time:                       0.
% 1.39/1.04  
% 1.39/1.04  ------ Problem properties
% 1.39/1.04  
% 1.39/1.04  clauses:                                10
% 1.39/1.04  conjectures:                            1
% 1.39/1.04  epr:                                    1
% 1.39/1.04  horn:                                   9
% 1.39/1.04  ground:                                 6
% 1.39/1.04  unary:                                  3
% 1.39/1.04  binary:                                 3
% 1.39/1.04  lits:                                   26
% 1.39/1.04  lits_eq:                                16
% 1.39/1.04  fd_pure:                                0
% 1.39/1.04  fd_pseudo:                              0
% 1.39/1.04  fd_cond:                                0
% 1.39/1.04  fd_pseudo_cond:                         0
% 1.39/1.04  ac_symbols:                             0
% 1.39/1.04  
% 1.39/1.04  ------ Propositional Solver
% 1.39/1.04  
% 1.39/1.04  prop_solver_calls:                      27
% 1.39/1.04  prop_fast_solver_calls:                 558
% 1.39/1.04  smt_solver_calls:                       0
% 1.39/1.04  smt_fast_solver_calls:                  0
% 1.39/1.04  prop_num_of_clauses:                    299
% 1.39/1.04  prop_preprocess_simplified:             1970
% 1.39/1.04  prop_fo_subsumed:                       9
% 1.39/1.04  prop_solver_time:                       0.
% 1.39/1.04  smt_solver_time:                        0.
% 1.39/1.04  smt_fast_solver_time:                   0.
% 1.39/1.04  prop_fast_solver_time:                  0.
% 1.39/1.04  prop_unsat_core_time:                   0.
% 1.39/1.04  
% 1.39/1.04  ------ QBF
% 1.39/1.04  
% 1.39/1.04  qbf_q_res:                              0
% 1.39/1.04  qbf_num_tautologies:                    0
% 1.39/1.04  qbf_prep_cycles:                        0
% 1.39/1.04  
% 1.39/1.04  ------ BMC1
% 1.39/1.04  
% 1.39/1.04  bmc1_current_bound:                     -1
% 1.39/1.04  bmc1_last_solved_bound:                 -1
% 1.39/1.04  bmc1_unsat_core_size:                   -1
% 1.39/1.04  bmc1_unsat_core_parents_size:           -1
% 1.39/1.04  bmc1_merge_next_fun:                    0
% 1.39/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.39/1.04  
% 1.39/1.04  ------ Instantiation
% 1.39/1.04  
% 1.39/1.04  inst_num_of_clauses:                    90
% 1.39/1.04  inst_num_in_passive:                    6
% 1.39/1.04  inst_num_in_active:                     79
% 1.39/1.04  inst_num_in_unprocessed:                5
% 1.39/1.04  inst_num_of_loops:                      90
% 1.39/1.04  inst_num_of_learning_restarts:          0
% 1.39/1.04  inst_num_moves_active_passive:          6
% 1.39/1.04  inst_lit_activity:                      0
% 1.39/1.04  inst_lit_activity_moves:                0
% 1.39/1.04  inst_num_tautologies:                   0
% 1.39/1.04  inst_num_prop_implied:                  0
% 1.39/1.04  inst_num_existing_simplified:           0
% 1.39/1.04  inst_num_eq_res_simplified:             0
% 1.39/1.04  inst_num_child_elim:                    0
% 1.39/1.04  inst_num_of_dismatching_blockings:      13
% 1.39/1.04  inst_num_of_non_proper_insts:           89
% 1.39/1.04  inst_num_of_duplicates:                 0
% 1.39/1.04  inst_inst_num_from_inst_to_res:         0
% 1.39/1.04  inst_dismatching_checking_time:         0.
% 1.39/1.04  
% 1.39/1.04  ------ Resolution
% 1.39/1.04  
% 1.39/1.04  res_num_of_clauses:                     0
% 1.39/1.04  res_num_in_passive:                     0
% 1.39/1.04  res_num_in_active:                      0
% 1.39/1.04  res_num_of_loops:                       92
% 1.39/1.04  res_forward_subset_subsumed:            36
% 1.39/1.04  res_backward_subset_subsumed:           0
% 1.39/1.04  res_forward_subsumed:                   0
% 1.39/1.04  res_backward_subsumed:                  0
% 1.39/1.04  res_forward_subsumption_resolution:     0
% 1.39/1.04  res_backward_subsumption_resolution:    0
% 1.39/1.04  res_clause_to_clause_subsumption:       23
% 1.39/1.04  res_orphan_elimination:                 0
% 1.39/1.04  res_tautology_del:                      31
% 1.39/1.04  res_num_eq_res_simplified:              0
% 1.39/1.04  res_num_sel_changes:                    0
% 1.39/1.04  res_moves_from_active_to_pass:          0
% 1.39/1.04  
% 1.39/1.04  ------ Superposition
% 1.39/1.04  
% 1.39/1.04  sup_time_total:                         0.
% 1.39/1.04  sup_time_generating:                    0.
% 1.39/1.04  sup_time_sim_full:                      0.
% 1.39/1.04  sup_time_sim_immed:                     0.
% 1.39/1.04  
% 1.39/1.04  sup_num_of_clauses:                     11
% 1.39/1.04  sup_num_in_active:                      11
% 1.39/1.04  sup_num_in_passive:                     0
% 1.39/1.04  sup_num_of_loops:                       16
% 1.39/1.04  sup_fw_superposition:                   0
% 1.39/1.04  sup_bw_superposition:                   0
% 1.39/1.04  sup_immediate_simplified:               0
% 1.39/1.04  sup_given_eliminated:                   0
% 1.39/1.04  comparisons_done:                       0
% 1.39/1.04  comparisons_avoided:                    0
% 1.39/1.04  
% 1.39/1.04  ------ Simplifications
% 1.39/1.04  
% 1.39/1.04  
% 1.39/1.04  sim_fw_subset_subsumed:                 0
% 1.39/1.04  sim_bw_subset_subsumed:                 0
% 1.39/1.04  sim_fw_subsumed:                        0
% 1.39/1.04  sim_bw_subsumed:                        0
% 1.39/1.04  sim_fw_subsumption_res:                 0
% 1.39/1.04  sim_bw_subsumption_res:                 0
% 1.39/1.04  sim_tautology_del:                      0
% 1.39/1.04  sim_eq_tautology_del:                   0
% 1.39/1.04  sim_eq_res_simp:                        0
% 1.39/1.04  sim_fw_demodulated:                     0
% 1.39/1.04  sim_bw_demodulated:                     5
% 1.39/1.04  sim_light_normalised:                   1
% 1.39/1.04  sim_joinable_taut:                      0
% 1.39/1.04  sim_joinable_simp:                      0
% 1.39/1.04  sim_ac_normalised:                      0
% 1.39/1.04  sim_smt_subsumption:                    0
% 1.39/1.04  
%------------------------------------------------------------------------------
