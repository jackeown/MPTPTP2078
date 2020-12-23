%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:13 EST 2020

% Result     : CounterSatisfiable 3.33s
% Output     : Saturation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  391 (10580 expanded)
%              Number of clauses        :  263 (3192 expanded)
%              Number of leaves         :   38 (2541 expanded)
%              Depth                    :   32
%              Number of atoms          : 1231 (67332 expanded)
%              Number of equality atoms :  514 (10231 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f134,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f106])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f26,conjecture,(
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

fof(f27,negated_conjecture,(
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
    inference(negated_conjecture,[],[f26])).

fof(f29,plain,(
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
    inference(pure_predicate_removal,[],[f27])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
            | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k2_funct_1(X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(X0)
          | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          | ~ v1_funct_2(k2_funct_1(sK6),u1_struct_0(X1),u1_struct_0(X0))
          | ~ v1_funct_1(k2_funct_1(sK6)) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
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
              | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
              | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(sK5),u1_struct_0(X0))
              | ~ v1_funct_1(k2_funct_1(X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK5))
            & v1_funct_1(X2) )
        & l1_orders_2(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
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
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK4)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK4))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,
    ( ( k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
      | ~ v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4))
      | ~ v1_funct_1(k2_funct_1(sK6)) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    & v1_funct_1(sK6)
    & l1_orders_2(sK5)
    & ~ v2_struct_0(sK5)
    & l1_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f63,f81,f80,f79])).

fof(f126,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f82])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f66])).

fof(f68,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f67,f68])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | r1_tarski(sK0(X0,X1),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f4,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f22,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK2(X0),X0)
        & k1_xboole_0 != sK2(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK2(X0),X0)
          & k1_xboole_0 != sK2(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f57,f73])).

fof(f113,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f132,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | ~ r1_tarski(sK0(X0,X1),X0)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f133,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f64])).

fof(f85,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1(X0))
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f70])).

fof(f93,plain,(
    ! [X0] : v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f71])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f86,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f127,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f82])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f128,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f82])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f75,plain,(
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
    inference(nnf_transformation,[],[f58])).

fof(f76,plain,(
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
    inference(flattening,[],[f75])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f119,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_yellow_0(X1,X0)
          & v1_orders_2(X1)
          & ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_orders_2(X1)
          & ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f31,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) )
     => ( ~ v2_struct_0(sK3(X0))
        & m1_yellow_0(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ( ~ v2_struct_0(sK3(X0))
        & m1_yellow_0(sK3(X0),X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f61,f77])).

fof(f120,plain,(
    ! [X0] :
      ( m1_yellow_0(sK3(X0),X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f124,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f82])).

fof(f125,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f82])).

fof(f121,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK3(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f112,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f122,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f82])).

fof(f123,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f82])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f130,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f43])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f129,plain,
    ( k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f82])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f135,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f108])).

fof(f115,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f136,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f110])).

fof(f114,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK2(X0)
      | k1_xboole_0 = k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_22,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v4_relat_1(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_691,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_692,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_702,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_692,c_13])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_797,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_42])).

cnf(c_798,plain,
    ( v1_funct_2(sK6,X0,X1)
    | ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_731,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = X1
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_42])).

cnf(c_732,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k8_relset_1(X0,X1,sK6,X1) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_1140,plain,
    ( ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k8_relset_1(X0,X1,sK6,X1) = X0
    | k1_xboole_0 = X1 ),
    inference(resolution,[status(thm)],[c_798,c_732])).

cnf(c_1344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k8_relset_1(X2,X3,sK6,X3) = X2
    | k1_relat_1(X0) != X2
    | sK6 != X0
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_702,c_1140])).

cnf(c_1345,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X1)))
    | k8_relset_1(k1_relat_1(sK6),X1,sK6,X1) = k1_relat_1(sK6)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_1344])).

cnf(c_2021,plain,
    ( sP2_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1345])).

cnf(c_544,plain,
    ( ~ m1_yellow_0(X0,X1)
    | m1_yellow_0(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_540,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_539,plain,
    ( ~ v1_partfun1(X0,X1)
    | v1_partfun1(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_538,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_534,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_2027,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(sK0(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3081,plain,
    ( k1_zfmisc_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_tarski(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3068,plain,
    ( k3_tarski(X0) != k1_xboole_0
    | k1_xboole_0 = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5212,plain,
    ( k1_xboole_0 != X0
    | k1_xboole_0 = X1
    | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_3068])).

cnf(c_5218,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5212])).

cnf(c_5864,plain,
    ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(sK0(X0,k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3081,c_5218])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_3080,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r1_tarski(sK0(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3082,plain,
    ( k1_zfmisc_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(sK0(X0,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5904,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) != iProver_top
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_3082])).

cnf(c_9070,plain,
    ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(sK0(X0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5864,c_5904])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_3079,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5863,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) = iProver_top
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3081,c_3079])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3085,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9040,plain,
    ( sK0(X0,k1_zfmisc_1(X1)) = X0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(X0,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5863,c_3085])).

cnf(c_9037,plain,
    ( sK0(X0,k1_zfmisc_1(X1)) = X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(X1,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5863,c_3085])).

cnf(c_5469,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_5218])).

cnf(c_5862,plain,
    ( sK0(k1_xboole_0,X0) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3081,c_5469])).

cnf(c_7671,plain,
    ( sK0(k1_xboole_0,k1_zfmisc_1(X0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(sK0(k1_xboole_0,k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5862,c_3079])).

cnf(c_8873,plain,
    ( sK0(k1_xboole_0,k1_zfmisc_1(X0)) = X0
    | sK0(k1_xboole_0,k1_zfmisc_1(X0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(X0,sK0(k1_xboole_0,k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7671,c_3085])).

cnf(c_9,plain,
    ( v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3078,plain,
    ( v1_xboole_0(sK1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3083,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4188,plain,
    ( sK1(X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3078,c_3083])).

cnf(c_10,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3077,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4863,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4188,c_3077])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_12])).

cnf(c_678,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_674,c_14,c_13,c_12])).

cnf(c_3060,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_5680,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4863,c_3060])).

cnf(c_3075,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5014,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4863,c_3075])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3076,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5128,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_5014,c_3076])).

cnf(c_8701,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5680,c_5128])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3073,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5801,plain,
    ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_4863,c_3073])).

cnf(c_8705,plain,
    ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8701,c_5801])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3071,plain,
    ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6564,plain,
    ( k8_relset_1(X0,X1,k1_xboole_0,k7_relset_1(X0,X1,k1_xboole_0,X0)) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4863,c_3071])).

cnf(c_6963,plain,
    ( k8_relset_1(X0,X1,k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6564,c_5801])).

cnf(c_8704,plain,
    ( k8_relset_1(X0,X1,k1_xboole_0,k2_relat_1(k1_xboole_0)) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8701,c_6963])).

cnf(c_23,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_654,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_14,c_23])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_23,c_14,c_13])).

cnf(c_659,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_658])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_764,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_42])).

cnf(c_765,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_1191,plain,
    ( v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | u1_struct_0(sK5) != X1
    | u1_struct_0(sK4) != X0
    | sK6 != sK6
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_765])).

cnf(c_1192,plain,
    ( v1_partfun1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | k1_xboole_0 = u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1191])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1194,plain,
    ( v1_partfun1(sK6,u1_struct_0(sK4))
    | k1_xboole_0 = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1192,c_40])).

cnf(c_1329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | u1_struct_0(sK5) = k1_xboole_0
    | u1_struct_0(sK4) != X1
    | k1_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_659,c_1194])).

cnf(c_1330,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0)))
    | u1_struct_0(sK5) = k1_xboole_0
    | k1_relat_1(sK6) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1329])).

cnf(c_2023,plain,
    ( sP3_iProver_split
    | u1_struct_0(sK5) = k1_xboole_0
    | k1_relat_1(sK6) = u1_struct_0(sK4) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1330])).

cnf(c_3049,plain,
    ( u1_struct_0(sK5) = k1_xboole_0
    | k1_relat_1(sK6) = u1_struct_0(sK4)
    | sP3_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2023])).

cnf(c_3066,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2022,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0)))
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_1330])).

cnf(c_3050,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2022])).

cnf(c_3637,plain,
    ( sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3066,c_3050])).

cnf(c_3638,plain,
    ( ~ sP3_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3637])).

cnf(c_3861,plain,
    ( k1_relat_1(sK6) = u1_struct_0(sK4)
    | u1_struct_0(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3049,c_2023,c_3638])).

cnf(c_3862,plain,
    ( u1_struct_0(sK5) = k1_xboole_0
    | k1_relat_1(sK6) = u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_3861])).

cnf(c_35,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_36,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_262,plain,
    ( ~ l1_orders_2(X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_yellow_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_35,c_36])).

cnf(c_263,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_262])).

cnf(c_38,plain,
    ( m1_yellow_0(sK3(X0),X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1097,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | X2 != X1
    | sK3(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_263,c_38])).

cnf(c_1098,plain,
    ( r1_tarski(u1_struct_0(sK3(X0)),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1097])).

cnf(c_3058,plain,
    ( r1_tarski(u1_struct_0(sK3(X0)),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1098])).

cnf(c_5694,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK6)
    | r1_tarski(u1_struct_0(sK3(sK5)),k1_xboole_0) = iProver_top
    | l1_orders_2(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3862,c_3058])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_49,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_50,plain,
    ( l1_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_6146,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK6)
    | r1_tarski(u1_struct_0(sK3(sK5)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5694,c_49,c_50])).

cnf(c_6153,plain,
    ( u1_struct_0(sK3(sK5)) = k1_xboole_0
    | u1_struct_0(sK4) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_6146,c_5469])).

cnf(c_135,plain,
    ( v1_xboole_0(sK1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_589,plain,
    ( sK1(X0) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_9])).

cnf(c_590,plain,
    ( k1_xboole_0 = sK1(X0) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_591,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_37,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3429,plain,
    ( ~ l1_orders_2(sK5)
    | ~ v2_struct_0(sK3(sK5))
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_1112,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X2)
    | v2_struct_0(X1)
    | X1 != X0
    | sK3(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_38])).

cnf(c_1113,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(sK3(X0))
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1112])).

cnf(c_3445,plain,
    ( l1_orders_2(sK3(sK5))
    | ~ l1_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_2031,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3523,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK1(X1))
    | X0 != sK1(X1) ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_3525,plain,
    ( ~ v1_xboole_0(sK1(k1_xboole_0))
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3523])).

cnf(c_29,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_28,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_613,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_29,c_28])).

cnf(c_3593,plain,
    ( ~ l1_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ v1_xboole_0(u1_struct_0(sK3(sK5))) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_4357,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK3(sK5)))
    | u1_struct_0(sK3(sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_4359,plain,
    ( v1_xboole_0(u1_struct_0(sK3(sK5)))
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(sK3(sK5)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4357])).

cnf(c_6158,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6153,c_44,c_43,c_135,c_591,c_3429,c_3445,c_3525,c_3593,c_4359])).

cnf(c_6234,plain,
    ( r1_tarski(u1_struct_0(sK3(sK4)),k1_relat_1(sK6)) = iProver_top
    | l1_orders_2(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6158,c_3058])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_47,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_48,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_8436,plain,
    ( r1_tarski(u1_struct_0(sK3(sK4)),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6234,c_47,c_48])).

cnf(c_8441,plain,
    ( u1_struct_0(sK3(sK4)) = k1_relat_1(sK6)
    | r1_tarski(k1_relat_1(sK6),u1_struct_0(sK3(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8436,c_3085])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_3084,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6178,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK5)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6158,c_3066])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3072,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6576,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6178,c_3072])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,k8_relset_1(X1,X2,X0,X2)) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3070,plain,
    ( k7_relset_1(X0,X1,X2,k8_relset_1(X0,X1,X2,X1)) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6802,plain,
    ( k7_relset_1(k1_relat_1(sK6),X0,sK6,k8_relset_1(k1_relat_1(sK6),X0,sK6,X0)) = k2_relset_1(k1_relat_1(sK6),X0,sK6)
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6576,c_3070])).

cnf(c_7276,plain,
    ( k7_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k2_relat_1(sK6))) = k2_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) ),
    inference(superposition,[status(thm)],[c_3084,c_6802])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3074,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6804,plain,
    ( k2_relset_1(k1_relat_1(sK6),X0,sK6) = k2_relat_1(sK6)
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6576,c_3074])).

cnf(c_6969,plain,
    ( k2_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_3084,c_6804])).

cnf(c_7277,plain,
    ( k7_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k2_relat_1(sK6))) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_7276,c_6969])).

cnf(c_6801,plain,
    ( k8_relset_1(k1_relat_1(sK6),X0,sK6,k7_relset_1(k1_relat_1(sK6),X0,sK6,k1_relat_1(sK6))) = k1_relset_1(k1_relat_1(sK6),X0,sK6)
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6576,c_3071])).

cnf(c_7281,plain,
    ( k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k7_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k1_relat_1(sK6))) = k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) ),
    inference(superposition,[status(thm)],[c_3084,c_6801])).

cnf(c_6803,plain,
    ( k7_relset_1(k1_relat_1(sK6),X0,sK6,X1) = k9_relat_1(sK6,X1)
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6576,c_3073])).

cnf(c_7142,plain,
    ( k7_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_3084,c_6803])).

cnf(c_7483,plain,
    ( k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k9_relat_1(sK6,k1_relat_1(sK6))) = k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) ),
    inference(demodulation,[status(thm)],[c_7281,c_7142])).

cnf(c_5678,plain,
    ( k7_relat_1(sK6,u1_struct_0(sK4)) = sK6 ),
    inference(superposition,[status(thm)],[c_3066,c_3060])).

cnf(c_4721,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3066,c_3075])).

cnf(c_4796,plain,
    ( k2_relat_1(k7_relat_1(sK6,X0)) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_4721,c_3076])).

cnf(c_5930,plain,
    ( k9_relat_1(sK6,u1_struct_0(sK4)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_5678,c_4796])).

cnf(c_6162,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_6158,c_5930])).

cnf(c_7484,plain,
    ( k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k2_relat_1(sK6)) = k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) ),
    inference(light_normalisation,[status(thm)],[c_7483,c_6162])).

cnf(c_8174,plain,
    ( k7_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6)) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_7277,c_7484])).

cnf(c_8178,plain,
    ( k9_relat_1(sK6,k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_8174,c_7142])).

cnf(c_3061,plain,
    ( l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_6935,plain,
    ( l1_orders_2(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6158,c_3061])).

cnf(c_7761,plain,
    ( v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6935,c_47,c_48])).

cnf(c_7748,plain,
    ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = X0
    | sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(X0,sK0(X0,k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5864,c_3085])).

cnf(c_7670,plain,
    ( sK0(k1_xboole_0,X0) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = X0
    | r1_tarski(sK0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5862,c_3082])).

cnf(c_2020,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)))
    | k8_relset_1(k1_relat_1(sK6),X0,sK6,X0) = k1_relat_1(sK6)
    | k1_xboole_0 = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_1345])).

cnf(c_3048,plain,
    ( k8_relset_1(k1_relat_1(sK6),X0,sK6,X0) = k1_relat_1(sK6)
    | k1_xboole_0 = X0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2020])).

cnf(c_39,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_812,plain,
    ( ~ v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | k2_funct_1(sK6) != sK6
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_39,c_42])).

cnf(c_1172,plain,
    ( ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_funct_1(sK6) != sK6
    | u1_struct_0(sK5) != X0
    | u1_struct_0(sK4) != X1
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_812,c_798])).

cnf(c_1173,plain,
    ( ~ v1_partfun1(sK6,u1_struct_0(sK5))
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | k2_funct_1(sK6) != sK6
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1172])).

cnf(c_1380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | k2_funct_1(sK6) != sK6
    | k1_relat_1(X0) != u1_struct_0(sK5)
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_702,c_1173])).

cnf(c_1381,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)))
    | k2_funct_1(sK6) != sK6
    | k1_relat_1(sK6) != u1_struct_0(sK5)
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1380])).

cnf(c_2017,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1381])).

cnf(c_2071,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2017])).

cnf(c_2077,plain,
    ( sP2_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2021])).

cnf(c_2079,plain,
    ( k8_relset_1(k1_relat_1(sK6),X0,sK6,X0) = k1_relat_1(sK6)
    | k1_xboole_0 = X0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2020])).

cnf(c_4662,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top
    | k1_xboole_0 = X0
    | k8_relset_1(k1_relat_1(sK6),X0,sK6,X0) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3048,c_2071,c_2077,c_2079])).

cnf(c_4663,plain,
    ( k8_relset_1(k1_relat_1(sK6),X0,sK6,X0) = k1_relat_1(sK6)
    | k1_xboole_0 = X0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4662])).

cnf(c_6805,plain,
    ( k8_relset_1(k1_relat_1(sK6),X0,sK6,X0) = k1_relat_1(sK6)
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6576,c_4663])).

cnf(c_7368,plain,
    ( k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k2_relat_1(sK6)) = k1_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3084,c_6805])).

cnf(c_7551,plain,
    ( k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) = k1_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7368,c_7484])).

cnf(c_6565,plain,
    ( k8_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,k7_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,k1_relat_1(sK6))) = k1_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6) ),
    inference(superposition,[status(thm)],[c_6178,c_3071])).

cnf(c_6452,plain,
    ( k7_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,k8_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,u1_struct_0(sK5))) = k2_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6) ),
    inference(superposition,[status(thm)],[c_6178,c_3070])).

cnf(c_5301,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_3066,c_3074])).

cnf(c_6166,plain,
    ( k2_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6) = k2_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_6158,c_5301])).

cnf(c_1406,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k8_relset_1(X0,X1,sK6,X1) = X0
    | u1_struct_0(sK5) = k1_xboole_0
    | u1_struct_0(sK4) != X0
    | sK6 != sK6
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1140,c_1194])).

cnf(c_1407,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0)))
    | k8_relset_1(u1_struct_0(sK4),X0,sK6,X0) = u1_struct_0(sK4)
    | u1_struct_0(sK5) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_1406])).

cnf(c_3040,plain,
    ( k8_relset_1(u1_struct_0(sK4),X0,sK6,X0) = u1_struct_0(sK4)
    | u1_struct_0(sK5) = k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1407])).

cnf(c_4017,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,u1_struct_0(sK5)) = u1_struct_0(sK4)
    | u1_struct_0(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3066,c_3040])).

cnf(c_3439,plain,
    ( ~ l1_orders_2(sK5)
    | v2_struct_0(sK5)
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_4347,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK5))
    | u1_struct_0(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_4349,plain,
    ( v1_xboole_0(u1_struct_0(sK5))
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4347])).

cnf(c_4377,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,u1_struct_0(sK5)) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4017,c_44,c_43,c_135,c_591,c_3439,c_3525,c_4349])).

cnf(c_6170,plain,
    ( k8_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,u1_struct_0(sK5)) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_6158,c_4377])).

cnf(c_6902,plain,
    ( k7_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_6452,c_6166,c_6170])).

cnf(c_6907,plain,
    ( k8_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,k2_relat_1(sK6)) = k1_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6) ),
    inference(light_normalisation,[status(thm)],[c_6565,c_6902])).

cnf(c_34,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_267,plain,
    ( ~ l1_orders_2(X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ m1_yellow_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34,c_36])).

cnf(c_268,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_267])).

cnf(c_1082,plain,
    ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | X2 != X1
    | sK3(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_268,c_38])).

cnf(c_1083,plain,
    ( r1_tarski(u1_orders_2(sK3(X0)),u1_orders_2(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1082])).

cnf(c_3059,plain,
    ( r1_tarski(u1_orders_2(sK3(X0)),u1_orders_2(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1083])).

cnf(c_6444,plain,
    ( u1_orders_2(sK3(X0)) = u1_orders_2(X0)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(sK3(X0))) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3059,c_3085])).

cnf(c_3042,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2017])).

cnf(c_6385,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_6178,c_3042])).

cnf(c_1157,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | k2_funct_1(sK6) != sK6
    | u1_struct_0(sK5) != u1_struct_0(sK4)
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_812,c_41])).

cnf(c_3056,plain,
    ( k2_funct_1(sK6) != sK6
    | u1_struct_0(sK5) != u1_struct_0(sK4)
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1157])).

cnf(c_6176,plain,
    ( k2_funct_1(sK6) != sK6
    | u1_struct_0(sK5) != k1_relat_1(sK6)
    | k2_relat_1(k2_funct_1(sK6)) != k1_relat_1(sK6)
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_relat_1(sK6)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6158,c_3056])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_782,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_42])).

cnf(c_783,plain,
    ( ~ v1_funct_2(sK6,k1_xboole_0,X0)
    | v1_partfun1(sK6,k1_xboole_0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
    inference(unflattening,[status(thm)],[c_782])).

cnf(c_1216,plain,
    ( v1_partfun1(sK6,k1_xboole_0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | u1_struct_0(sK5) != X0
    | u1_struct_0(sK4) != k1_xboole_0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_783])).

cnf(c_1217,plain,
    ( v1_partfun1(sK6,k1_xboole_0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
    | u1_struct_0(sK4) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1216])).

cnf(c_1311,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
    | u1_struct_0(sK4) != k1_xboole_0
    | k1_relat_1(X0) = X1
    | sK6 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_659,c_1217])).

cnf(c_1312,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
    | u1_struct_0(sK4) != k1_xboole_0
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1311])).

cnf(c_2025,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
    | sP4_iProver_split
    | u1_struct_0(sK4) != k1_xboole_0
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1312])).

cnf(c_3051,plain,
    ( u1_struct_0(sK4) != k1_xboole_0
    | k1_relat_1(sK6) = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5)))) != iProver_top
    | sP4_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2025])).

cnf(c_2024,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_1312])).

cnf(c_3052,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2024])).

cnf(c_3260,plain,
    ( u1_struct_0(sK4) != k1_xboole_0
    | k1_relat_1(sK6) = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3051,c_3052])).

cnf(c_3442,plain,
    ( ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_4352,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK4))
    | u1_struct_0(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_4354,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4352])).

cnf(c_4443,plain,
    ( u1_struct_0(sK4) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3260,c_46,c_45,c_135,c_591,c_3442,c_3525,c_4354])).

cnf(c_6168,plain,
    ( k1_relat_1(sK6) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6158,c_4443])).

cnf(c_6164,plain,
    ( k7_relat_1(sK6,k1_relat_1(sK6)) = sK6 ),
    inference(demodulation,[status(thm)],[c_6158,c_5678])).

cnf(c_5799,plain,
    ( k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_3066,c_3073])).

cnf(c_6163,plain,
    ( k7_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(demodulation,[status(thm)],[c_6158,c_5799])).

cnf(c_5861,plain,
    ( sK0(X0,X1) = X0
    | k1_zfmisc_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_tarski(X0,sK0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3081,c_3085])).

cnf(c_5777,plain,
    ( u1_struct_0(sK3(X0)) = u1_struct_0(X0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3(X0))) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3058,c_3085])).

cnf(c_30,plain,
    ( r2_hidden(sK2(X0),X0)
    | k3_tarski(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3069,plain,
    ( k3_tarski(X0) = k1_xboole_0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4261,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = k1_xboole_0
    | r1_tarski(sK2(k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3069,c_3079])).

cnf(c_4262,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(sK2(k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4261,c_8])).

cnf(c_5776,plain,
    ( sK2(k1_zfmisc_1(X0)) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK2(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4262,c_3085])).

cnf(c_5303,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4863,c_3074])).

cnf(c_4864,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4188,c_3078])).

cnf(c_3046,plain,
    ( sP2_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2021])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(k1_xboole_0,X1,X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_749,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k8_relset_1(k1_xboole_0,X1,X0,X1) = k1_xboole_0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_42])).

cnf(c_750,plain,
    ( ~ v1_funct_2(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k8_relset_1(k1_xboole_0,X0,sK6,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_749])).

cnf(c_1244,plain,
    ( ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | X2 != X1
    | k8_relset_1(k1_xboole_0,X2,sK6,X2) = k1_xboole_0
    | sK6 != sK6
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_798,c_750])).

cnf(c_1245,plain,
    ( ~ v1_partfun1(sK6,k1_xboole_0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k8_relset_1(k1_xboole_0,X0,sK6,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1244])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k8_relset_1(k1_xboole_0,X0,sK6,X0) = k1_xboole_0
    | u1_struct_0(sK5) = k1_xboole_0
    | u1_struct_0(sK4) != k1_xboole_0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_1245,c_1194])).

cnf(c_1568,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k8_relset_1(k1_xboole_0,X0,sK6,X0) = k1_xboole_0
    | u1_struct_0(sK5) = k1_xboole_0
    | u1_struct_0(sK4) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1451])).

cnf(c_2015,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k8_relset_1(k1_xboole_0,X0,sK6,X0) = k1_xboole_0
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1568])).

cnf(c_3039,plain,
    ( k8_relset_1(k1_xboole_0,X0,sK6,X0) = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2015])).

cnf(c_3057,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK3(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1113])).

cnf(c_3067,plain,
    ( l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3065,plain,
    ( l1_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_3064,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_3063,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_3062,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_31,plain,
    ( sK2(X0) != k1_xboole_0
    | k3_tarski(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:09:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.33/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.01  
% 3.33/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/1.01  
% 3.33/1.01  ------  iProver source info
% 3.33/1.01  
% 3.33/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.33/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/1.01  git: non_committed_changes: false
% 3.33/1.01  git: last_make_outside_of_git: false
% 3.33/1.01  
% 3.33/1.01  ------ 
% 3.33/1.01  
% 3.33/1.01  ------ Input Options
% 3.33/1.01  
% 3.33/1.01  --out_options                           all
% 3.33/1.01  --tptp_safe_out                         true
% 3.33/1.01  --problem_path                          ""
% 3.33/1.01  --include_path                          ""
% 3.33/1.01  --clausifier                            res/vclausify_rel
% 3.33/1.01  --clausifier_options                    --mode clausify
% 3.33/1.01  --stdin                                 false
% 3.33/1.01  --stats_out                             all
% 3.33/1.01  
% 3.33/1.01  ------ General Options
% 3.33/1.01  
% 3.33/1.01  --fof                                   false
% 3.33/1.01  --time_out_real                         305.
% 3.33/1.01  --time_out_virtual                      -1.
% 3.33/1.01  --symbol_type_check                     false
% 3.33/1.01  --clausify_out                          false
% 3.33/1.01  --sig_cnt_out                           false
% 3.33/1.01  --trig_cnt_out                          false
% 3.33/1.01  --trig_cnt_out_tolerance                1.
% 3.33/1.01  --trig_cnt_out_sk_spl                   false
% 3.33/1.01  --abstr_cl_out                          false
% 3.33/1.01  
% 3.33/1.01  ------ Global Options
% 3.33/1.01  
% 3.33/1.01  --schedule                              default
% 3.33/1.01  --add_important_lit                     false
% 3.33/1.01  --prop_solver_per_cl                    1000
% 3.33/1.01  --min_unsat_core                        false
% 3.33/1.01  --soft_assumptions                      false
% 3.33/1.01  --soft_lemma_size                       3
% 3.33/1.01  --prop_impl_unit_size                   0
% 3.33/1.01  --prop_impl_unit                        []
% 3.33/1.01  --share_sel_clauses                     true
% 3.33/1.01  --reset_solvers                         false
% 3.33/1.01  --bc_imp_inh                            [conj_cone]
% 3.33/1.01  --conj_cone_tolerance                   3.
% 3.33/1.01  --extra_neg_conj                        none
% 3.33/1.01  --large_theory_mode                     true
% 3.33/1.01  --prolific_symb_bound                   200
% 3.33/1.01  --lt_threshold                          2000
% 3.33/1.01  --clause_weak_htbl                      true
% 3.33/1.01  --gc_record_bc_elim                     false
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing Options
% 3.33/1.01  
% 3.33/1.01  --preprocessing_flag                    true
% 3.33/1.01  --time_out_prep_mult                    0.1
% 3.33/1.01  --splitting_mode                        input
% 3.33/1.01  --splitting_grd                         true
% 3.33/1.01  --splitting_cvd                         false
% 3.33/1.01  --splitting_cvd_svl                     false
% 3.33/1.01  --splitting_nvd                         32
% 3.33/1.01  --sub_typing                            true
% 3.33/1.01  --prep_gs_sim                           true
% 3.33/1.01  --prep_unflatten                        true
% 3.33/1.01  --prep_res_sim                          true
% 3.33/1.01  --prep_upred                            true
% 3.33/1.01  --prep_sem_filter                       exhaustive
% 3.33/1.01  --prep_sem_filter_out                   false
% 3.33/1.01  --pred_elim                             true
% 3.33/1.01  --res_sim_input                         true
% 3.33/1.01  --eq_ax_congr_red                       true
% 3.33/1.01  --pure_diseq_elim                       true
% 3.33/1.01  --brand_transform                       false
% 3.33/1.01  --non_eq_to_eq                          false
% 3.33/1.01  --prep_def_merge                        true
% 3.33/1.01  --prep_def_merge_prop_impl              false
% 3.33/1.01  --prep_def_merge_mbd                    true
% 3.33/1.01  --prep_def_merge_tr_red                 false
% 3.33/1.01  --prep_def_merge_tr_cl                  false
% 3.33/1.01  --smt_preprocessing                     true
% 3.33/1.01  --smt_ac_axioms                         fast
% 3.33/1.01  --preprocessed_out                      false
% 3.33/1.01  --preprocessed_stats                    false
% 3.33/1.01  
% 3.33/1.01  ------ Abstraction refinement Options
% 3.33/1.01  
% 3.33/1.01  --abstr_ref                             []
% 3.33/1.01  --abstr_ref_prep                        false
% 3.33/1.01  --abstr_ref_until_sat                   false
% 3.33/1.01  --abstr_ref_sig_restrict                funpre
% 3.33/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.01  --abstr_ref_under                       []
% 3.33/1.01  
% 3.33/1.01  ------ SAT Options
% 3.33/1.01  
% 3.33/1.01  --sat_mode                              false
% 3.33/1.01  --sat_fm_restart_options                ""
% 3.33/1.01  --sat_gr_def                            false
% 3.33/1.01  --sat_epr_types                         true
% 3.33/1.01  --sat_non_cyclic_types                  false
% 3.33/1.01  --sat_finite_models                     false
% 3.33/1.01  --sat_fm_lemmas                         false
% 3.33/1.01  --sat_fm_prep                           false
% 3.33/1.01  --sat_fm_uc_incr                        true
% 3.33/1.01  --sat_out_model                         small
% 3.33/1.01  --sat_out_clauses                       false
% 3.33/1.01  
% 3.33/1.01  ------ QBF Options
% 3.33/1.01  
% 3.33/1.01  --qbf_mode                              false
% 3.33/1.01  --qbf_elim_univ                         false
% 3.33/1.01  --qbf_dom_inst                          none
% 3.33/1.01  --qbf_dom_pre_inst                      false
% 3.33/1.01  --qbf_sk_in                             false
% 3.33/1.01  --qbf_pred_elim                         true
% 3.33/1.01  --qbf_split                             512
% 3.33/1.01  
% 3.33/1.01  ------ BMC1 Options
% 3.33/1.01  
% 3.33/1.01  --bmc1_incremental                      false
% 3.33/1.01  --bmc1_axioms                           reachable_all
% 3.33/1.01  --bmc1_min_bound                        0
% 3.33/1.01  --bmc1_max_bound                        -1
% 3.33/1.01  --bmc1_max_bound_default                -1
% 3.33/1.01  --bmc1_symbol_reachability              true
% 3.33/1.01  --bmc1_property_lemmas                  false
% 3.33/1.01  --bmc1_k_induction                      false
% 3.33/1.01  --bmc1_non_equiv_states                 false
% 3.33/1.01  --bmc1_deadlock                         false
% 3.33/1.01  --bmc1_ucm                              false
% 3.33/1.01  --bmc1_add_unsat_core                   none
% 3.33/1.01  --bmc1_unsat_core_children              false
% 3.33/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.01  --bmc1_out_stat                         full
% 3.33/1.01  --bmc1_ground_init                      false
% 3.33/1.01  --bmc1_pre_inst_next_state              false
% 3.33/1.01  --bmc1_pre_inst_state                   false
% 3.33/1.01  --bmc1_pre_inst_reach_state             false
% 3.33/1.01  --bmc1_out_unsat_core                   false
% 3.33/1.01  --bmc1_aig_witness_out                  false
% 3.33/1.01  --bmc1_verbose                          false
% 3.33/1.01  --bmc1_dump_clauses_tptp                false
% 3.33/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.01  --bmc1_dump_file                        -
% 3.33/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.01  --bmc1_ucm_extend_mode                  1
% 3.33/1.01  --bmc1_ucm_init_mode                    2
% 3.33/1.01  --bmc1_ucm_cone_mode                    none
% 3.33/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.01  --bmc1_ucm_relax_model                  4
% 3.33/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.01  --bmc1_ucm_layered_model                none
% 3.33/1.01  --bmc1_ucm_max_lemma_size               10
% 3.33/1.01  
% 3.33/1.01  ------ AIG Options
% 3.33/1.01  
% 3.33/1.01  --aig_mode                              false
% 3.33/1.01  
% 3.33/1.01  ------ Instantiation Options
% 3.33/1.01  
% 3.33/1.01  --instantiation_flag                    true
% 3.33/1.01  --inst_sos_flag                         false
% 3.33/1.01  --inst_sos_phase                        true
% 3.33/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.01  --inst_lit_sel_side                     num_symb
% 3.33/1.01  --inst_solver_per_active                1400
% 3.33/1.01  --inst_solver_calls_frac                1.
% 3.33/1.01  --inst_passive_queue_type               priority_queues
% 3.33/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.01  --inst_passive_queues_freq              [25;2]
% 3.33/1.01  --inst_dismatching                      true
% 3.33/1.01  --inst_eager_unprocessed_to_passive     true
% 3.33/1.01  --inst_prop_sim_given                   true
% 3.33/1.01  --inst_prop_sim_new                     false
% 3.33/1.01  --inst_subs_new                         false
% 3.33/1.01  --inst_eq_res_simp                      false
% 3.33/1.01  --inst_subs_given                       false
% 3.33/1.01  --inst_orphan_elimination               true
% 3.33/1.01  --inst_learning_loop_flag               true
% 3.33/1.01  --inst_learning_start                   3000
% 3.33/1.01  --inst_learning_factor                  2
% 3.33/1.01  --inst_start_prop_sim_after_learn       3
% 3.33/1.01  --inst_sel_renew                        solver
% 3.33/1.01  --inst_lit_activity_flag                true
% 3.33/1.01  --inst_restr_to_given                   false
% 3.33/1.01  --inst_activity_threshold               500
% 3.33/1.01  --inst_out_proof                        true
% 3.33/1.01  
% 3.33/1.01  ------ Resolution Options
% 3.33/1.01  
% 3.33/1.01  --resolution_flag                       true
% 3.33/1.01  --res_lit_sel                           adaptive
% 3.33/1.01  --res_lit_sel_side                      none
% 3.33/1.01  --res_ordering                          kbo
% 3.33/1.01  --res_to_prop_solver                    active
% 3.33/1.01  --res_prop_simpl_new                    false
% 3.33/1.01  --res_prop_simpl_given                  true
% 3.33/1.01  --res_passive_queue_type                priority_queues
% 3.33/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.01  --res_passive_queues_freq               [15;5]
% 3.33/1.01  --res_forward_subs                      full
% 3.33/1.01  --res_backward_subs                     full
% 3.33/1.01  --res_forward_subs_resolution           true
% 3.33/1.01  --res_backward_subs_resolution          true
% 3.33/1.01  --res_orphan_elimination                true
% 3.33/1.01  --res_time_limit                        2.
% 3.33/1.01  --res_out_proof                         true
% 3.33/1.01  
% 3.33/1.01  ------ Superposition Options
% 3.33/1.01  
% 3.33/1.01  --superposition_flag                    true
% 3.33/1.01  --sup_passive_queue_type                priority_queues
% 3.33/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.01  --demod_completeness_check              fast
% 3.33/1.01  --demod_use_ground                      true
% 3.33/1.01  --sup_to_prop_solver                    passive
% 3.33/1.01  --sup_prop_simpl_new                    true
% 3.33/1.01  --sup_prop_simpl_given                  true
% 3.33/1.01  --sup_fun_splitting                     false
% 3.33/1.01  --sup_smt_interval                      50000
% 3.33/1.01  
% 3.33/1.01  ------ Superposition Simplification Setup
% 3.33/1.01  
% 3.33/1.01  --sup_indices_passive                   []
% 3.33/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_full_bw                           [BwDemod]
% 3.33/1.01  --sup_immed_triv                        [TrivRules]
% 3.33/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_immed_bw_main                     []
% 3.33/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.01  
% 3.33/1.01  ------ Combination Options
% 3.33/1.01  
% 3.33/1.01  --comb_res_mult                         3
% 3.33/1.01  --comb_sup_mult                         2
% 3.33/1.01  --comb_inst_mult                        10
% 3.33/1.01  
% 3.33/1.01  ------ Debug Options
% 3.33/1.01  
% 3.33/1.01  --dbg_backtrace                         false
% 3.33/1.01  --dbg_dump_prop_clauses                 false
% 3.33/1.01  --dbg_dump_prop_clauses_file            -
% 3.33/1.01  --dbg_out_stat                          false
% 3.33/1.01  ------ Parsing...
% 3.33/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing... gs_s  sp: 9 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/1.01  ------ Proving...
% 3.33/1.01  ------ Problem Properties 
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  clauses                                 52
% 3.33/1.01  conjectures                             5
% 3.33/1.01  EPR                                     8
% 3.33/1.01  Horn                                    39
% 3.33/1.01  unary                                   9
% 3.33/1.01  binary                                  19
% 3.33/1.01  lits                                    130
% 3.33/1.01  lits eq                                 46
% 3.33/1.01  fd_pure                                 0
% 3.33/1.01  fd_pseudo                               0
% 3.33/1.01  fd_cond                                 4
% 3.33/1.01  fd_pseudo_cond                          3
% 3.33/1.01  AC symbols                              0
% 3.33/1.01  
% 3.33/1.01  ------ Schedule dynamic 5 is on 
% 3.33/1.01  
% 3.33/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  ------ 
% 3.33/1.01  Current options:
% 3.33/1.01  ------ 
% 3.33/1.01  
% 3.33/1.01  ------ Input Options
% 3.33/1.01  
% 3.33/1.01  --out_options                           all
% 3.33/1.01  --tptp_safe_out                         true
% 3.33/1.01  --problem_path                          ""
% 3.33/1.01  --include_path                          ""
% 3.33/1.01  --clausifier                            res/vclausify_rel
% 3.33/1.01  --clausifier_options                    --mode clausify
% 3.33/1.01  --stdin                                 false
% 3.33/1.01  --stats_out                             all
% 3.33/1.01  
% 3.33/1.01  ------ General Options
% 3.33/1.01  
% 3.33/1.01  --fof                                   false
% 3.33/1.01  --time_out_real                         305.
% 3.33/1.01  --time_out_virtual                      -1.
% 3.33/1.01  --symbol_type_check                     false
% 3.33/1.01  --clausify_out                          false
% 3.33/1.01  --sig_cnt_out                           false
% 3.33/1.01  --trig_cnt_out                          false
% 3.33/1.01  --trig_cnt_out_tolerance                1.
% 3.33/1.01  --trig_cnt_out_sk_spl                   false
% 3.33/1.01  --abstr_cl_out                          false
% 3.33/1.01  
% 3.33/1.01  ------ Global Options
% 3.33/1.01  
% 3.33/1.01  --schedule                              default
% 3.33/1.01  --add_important_lit                     false
% 3.33/1.01  --prop_solver_per_cl                    1000
% 3.33/1.01  --min_unsat_core                        false
% 3.33/1.01  --soft_assumptions                      false
% 3.33/1.01  --soft_lemma_size                       3
% 3.33/1.01  --prop_impl_unit_size                   0
% 3.33/1.01  --prop_impl_unit                        []
% 3.33/1.01  --share_sel_clauses                     true
% 3.33/1.01  --reset_solvers                         false
% 3.33/1.01  --bc_imp_inh                            [conj_cone]
% 3.33/1.01  --conj_cone_tolerance                   3.
% 3.33/1.01  --extra_neg_conj                        none
% 3.33/1.01  --large_theory_mode                     true
% 3.33/1.01  --prolific_symb_bound                   200
% 3.33/1.01  --lt_threshold                          2000
% 3.33/1.01  --clause_weak_htbl                      true
% 3.33/1.01  --gc_record_bc_elim                     false
% 3.33/1.01  
% 3.33/1.01  ------ Preprocessing Options
% 3.33/1.01  
% 3.33/1.01  --preprocessing_flag                    true
% 3.33/1.01  --time_out_prep_mult                    0.1
% 3.33/1.01  --splitting_mode                        input
% 3.33/1.01  --splitting_grd                         true
% 3.33/1.01  --splitting_cvd                         false
% 3.33/1.01  --splitting_cvd_svl                     false
% 3.33/1.01  --splitting_nvd                         32
% 3.33/1.01  --sub_typing                            true
% 3.33/1.01  --prep_gs_sim                           true
% 3.33/1.01  --prep_unflatten                        true
% 3.33/1.01  --prep_res_sim                          true
% 3.33/1.01  --prep_upred                            true
% 3.33/1.01  --prep_sem_filter                       exhaustive
% 3.33/1.01  --prep_sem_filter_out                   false
% 3.33/1.01  --pred_elim                             true
% 3.33/1.01  --res_sim_input                         true
% 3.33/1.01  --eq_ax_congr_red                       true
% 3.33/1.01  --pure_diseq_elim                       true
% 3.33/1.01  --brand_transform                       false
% 3.33/1.01  --non_eq_to_eq                          false
% 3.33/1.01  --prep_def_merge                        true
% 3.33/1.01  --prep_def_merge_prop_impl              false
% 3.33/1.01  --prep_def_merge_mbd                    true
% 3.33/1.01  --prep_def_merge_tr_red                 false
% 3.33/1.01  --prep_def_merge_tr_cl                  false
% 3.33/1.01  --smt_preprocessing                     true
% 3.33/1.01  --smt_ac_axioms                         fast
% 3.33/1.01  --preprocessed_out                      false
% 3.33/1.01  --preprocessed_stats                    false
% 3.33/1.01  
% 3.33/1.01  ------ Abstraction refinement Options
% 3.33/1.01  
% 3.33/1.01  --abstr_ref                             []
% 3.33/1.01  --abstr_ref_prep                        false
% 3.33/1.01  --abstr_ref_until_sat                   false
% 3.33/1.01  --abstr_ref_sig_restrict                funpre
% 3.33/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/1.01  --abstr_ref_under                       []
% 3.33/1.01  
% 3.33/1.01  ------ SAT Options
% 3.33/1.01  
% 3.33/1.01  --sat_mode                              false
% 3.33/1.01  --sat_fm_restart_options                ""
% 3.33/1.01  --sat_gr_def                            false
% 3.33/1.01  --sat_epr_types                         true
% 3.33/1.01  --sat_non_cyclic_types                  false
% 3.33/1.01  --sat_finite_models                     false
% 3.33/1.01  --sat_fm_lemmas                         false
% 3.33/1.01  --sat_fm_prep                           false
% 3.33/1.01  --sat_fm_uc_incr                        true
% 3.33/1.01  --sat_out_model                         small
% 3.33/1.01  --sat_out_clauses                       false
% 3.33/1.01  
% 3.33/1.01  ------ QBF Options
% 3.33/1.01  
% 3.33/1.01  --qbf_mode                              false
% 3.33/1.01  --qbf_elim_univ                         false
% 3.33/1.01  --qbf_dom_inst                          none
% 3.33/1.01  --qbf_dom_pre_inst                      false
% 3.33/1.01  --qbf_sk_in                             false
% 3.33/1.01  --qbf_pred_elim                         true
% 3.33/1.01  --qbf_split                             512
% 3.33/1.01  
% 3.33/1.01  ------ BMC1 Options
% 3.33/1.01  
% 3.33/1.01  --bmc1_incremental                      false
% 3.33/1.01  --bmc1_axioms                           reachable_all
% 3.33/1.01  --bmc1_min_bound                        0
% 3.33/1.01  --bmc1_max_bound                        -1
% 3.33/1.01  --bmc1_max_bound_default                -1
% 3.33/1.01  --bmc1_symbol_reachability              true
% 3.33/1.01  --bmc1_property_lemmas                  false
% 3.33/1.01  --bmc1_k_induction                      false
% 3.33/1.01  --bmc1_non_equiv_states                 false
% 3.33/1.01  --bmc1_deadlock                         false
% 3.33/1.01  --bmc1_ucm                              false
% 3.33/1.01  --bmc1_add_unsat_core                   none
% 3.33/1.01  --bmc1_unsat_core_children              false
% 3.33/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/1.01  --bmc1_out_stat                         full
% 3.33/1.01  --bmc1_ground_init                      false
% 3.33/1.01  --bmc1_pre_inst_next_state              false
% 3.33/1.01  --bmc1_pre_inst_state                   false
% 3.33/1.01  --bmc1_pre_inst_reach_state             false
% 3.33/1.01  --bmc1_out_unsat_core                   false
% 3.33/1.01  --bmc1_aig_witness_out                  false
% 3.33/1.01  --bmc1_verbose                          false
% 3.33/1.01  --bmc1_dump_clauses_tptp                false
% 3.33/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.33/1.01  --bmc1_dump_file                        -
% 3.33/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.33/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.33/1.01  --bmc1_ucm_extend_mode                  1
% 3.33/1.01  --bmc1_ucm_init_mode                    2
% 3.33/1.01  --bmc1_ucm_cone_mode                    none
% 3.33/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.33/1.01  --bmc1_ucm_relax_model                  4
% 3.33/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.33/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/1.01  --bmc1_ucm_layered_model                none
% 3.33/1.01  --bmc1_ucm_max_lemma_size               10
% 3.33/1.01  
% 3.33/1.01  ------ AIG Options
% 3.33/1.01  
% 3.33/1.01  --aig_mode                              false
% 3.33/1.01  
% 3.33/1.01  ------ Instantiation Options
% 3.33/1.01  
% 3.33/1.01  --instantiation_flag                    true
% 3.33/1.01  --inst_sos_flag                         false
% 3.33/1.01  --inst_sos_phase                        true
% 3.33/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/1.01  --inst_lit_sel_side                     none
% 3.33/1.01  --inst_solver_per_active                1400
% 3.33/1.01  --inst_solver_calls_frac                1.
% 3.33/1.01  --inst_passive_queue_type               priority_queues
% 3.33/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/1.01  --inst_passive_queues_freq              [25;2]
% 3.33/1.01  --inst_dismatching                      true
% 3.33/1.01  --inst_eager_unprocessed_to_passive     true
% 3.33/1.01  --inst_prop_sim_given                   true
% 3.33/1.01  --inst_prop_sim_new                     false
% 3.33/1.01  --inst_subs_new                         false
% 3.33/1.01  --inst_eq_res_simp                      false
% 3.33/1.01  --inst_subs_given                       false
% 3.33/1.01  --inst_orphan_elimination               true
% 3.33/1.01  --inst_learning_loop_flag               true
% 3.33/1.01  --inst_learning_start                   3000
% 3.33/1.01  --inst_learning_factor                  2
% 3.33/1.01  --inst_start_prop_sim_after_learn       3
% 3.33/1.01  --inst_sel_renew                        solver
% 3.33/1.01  --inst_lit_activity_flag                true
% 3.33/1.01  --inst_restr_to_given                   false
% 3.33/1.01  --inst_activity_threshold               500
% 3.33/1.01  --inst_out_proof                        true
% 3.33/1.01  
% 3.33/1.01  ------ Resolution Options
% 3.33/1.01  
% 3.33/1.01  --resolution_flag                       false
% 3.33/1.01  --res_lit_sel                           adaptive
% 3.33/1.01  --res_lit_sel_side                      none
% 3.33/1.01  --res_ordering                          kbo
% 3.33/1.01  --res_to_prop_solver                    active
% 3.33/1.01  --res_prop_simpl_new                    false
% 3.33/1.01  --res_prop_simpl_given                  true
% 3.33/1.01  --res_passive_queue_type                priority_queues
% 3.33/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/1.01  --res_passive_queues_freq               [15;5]
% 3.33/1.01  --res_forward_subs                      full
% 3.33/1.01  --res_backward_subs                     full
% 3.33/1.01  --res_forward_subs_resolution           true
% 3.33/1.01  --res_backward_subs_resolution          true
% 3.33/1.01  --res_orphan_elimination                true
% 3.33/1.01  --res_time_limit                        2.
% 3.33/1.01  --res_out_proof                         true
% 3.33/1.01  
% 3.33/1.01  ------ Superposition Options
% 3.33/1.01  
% 3.33/1.01  --superposition_flag                    true
% 3.33/1.01  --sup_passive_queue_type                priority_queues
% 3.33/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.33/1.01  --demod_completeness_check              fast
% 3.33/1.01  --demod_use_ground                      true
% 3.33/1.01  --sup_to_prop_solver                    passive
% 3.33/1.01  --sup_prop_simpl_new                    true
% 3.33/1.01  --sup_prop_simpl_given                  true
% 3.33/1.01  --sup_fun_splitting                     false
% 3.33/1.01  --sup_smt_interval                      50000
% 3.33/1.01  
% 3.33/1.01  ------ Superposition Simplification Setup
% 3.33/1.01  
% 3.33/1.01  --sup_indices_passive                   []
% 3.33/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_full_bw                           [BwDemod]
% 3.33/1.01  --sup_immed_triv                        [TrivRules]
% 3.33/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_immed_bw_main                     []
% 3.33/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/1.01  
% 3.33/1.01  ------ Combination Options
% 3.33/1.01  
% 3.33/1.01  --comb_res_mult                         3
% 3.33/1.01  --comb_sup_mult                         2
% 3.33/1.01  --comb_inst_mult                        10
% 3.33/1.01  
% 3.33/1.01  ------ Debug Options
% 3.33/1.01  
% 3.33/1.01  --dbg_backtrace                         false
% 3.33/1.01  --dbg_dump_prop_clauses                 false
% 3.33/1.01  --dbg_dump_prop_clauses_file            -
% 3.33/1.01  --dbg_out_stat                          false
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  ------ Proving...
% 3.33/1.01  
% 3.33/1.01  
% 3.33/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 3.33/1.01  
% 3.33/1.01  % SZS output start Saturation for theBenchmark.p
% 3.33/1.01  
% 3.33/1.01  fof(f10,axiom,(
% 3.33/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f32,plain,(
% 3.33/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.33/1.01    inference(pure_predicate_removal,[],[f10])).
% 3.33/1.01  
% 3.33/1.01  fof(f40,plain,(
% 3.33/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.01    inference(ennf_transformation,[],[f32])).
% 3.33/1.01  
% 3.33/1.01  fof(f97,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f40])).
% 3.33/1.01  
% 3.33/1.01  fof(f16,axiom,(
% 3.33/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f48,plain,(
% 3.33/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.33/1.01    inference(ennf_transformation,[],[f16])).
% 3.33/1.01  
% 3.33/1.01  fof(f49,plain,(
% 3.33/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(flattening,[],[f48])).
% 3.33/1.01  
% 3.33/1.01  fof(f72,plain,(
% 3.33/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(nnf_transformation,[],[f49])).
% 3.33/1.01  
% 3.33/1.01  fof(f106,plain,(
% 3.33/1.01    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f72])).
% 3.33/1.01  
% 3.33/1.01  fof(f134,plain,(
% 3.33/1.01    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.33/1.01    inference(equality_resolution,[],[f106])).
% 3.33/1.01  
% 3.33/1.01  fof(f9,axiom,(
% 3.33/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f39,plain,(
% 3.33/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.01    inference(ennf_transformation,[],[f9])).
% 3.33/1.01  
% 3.33/1.01  fof(f96,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f39])).
% 3.33/1.01  
% 3.33/1.01  fof(f15,axiom,(
% 3.33/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f46,plain,(
% 3.33/1.01    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.01    inference(ennf_transformation,[],[f15])).
% 3.33/1.01  
% 3.33/1.01  fof(f47,plain,(
% 3.33/1.01    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.01    inference(flattening,[],[f46])).
% 3.33/1.01  
% 3.33/1.01  fof(f104,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f47])).
% 3.33/1.01  
% 3.33/1.01  fof(f26,conjecture,(
% 3.33/1.01    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f27,negated_conjecture,(
% 3.33/1.01    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 3.33/1.01    inference(negated_conjecture,[],[f26])).
% 3.33/1.01  
% 3.33/1.01  fof(f29,plain,(
% 3.33/1.01    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 3.33/1.01    inference(pure_predicate_removal,[],[f27])).
% 3.33/1.01  
% 3.33/1.01  fof(f62,plain,(
% 3.33/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_orders_2(X1) & ~v2_struct_0(X1))) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f29])).
% 3.33/1.01  
% 3.33/1.01  fof(f63,plain,(
% 3.33/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 3.33/1.01    inference(flattening,[],[f62])).
% 3.33/1.01  
% 3.33/1.01  fof(f81,plain,(
% 3.33/1.01    ( ! [X0,X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(sK6),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(sK6))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f80,plain,(
% 3.33/1.01    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(sK5),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK5)) & v1_funct_1(X2)) & l1_orders_2(sK5) & ~v2_struct_0(sK5))) )),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f79,plain,(
% 3.33/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK4) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK4)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(sK4) & ~v2_struct_0(sK4))),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f82,plain,(
% 3.33/1.01    (((k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) | ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_funct_1(sK6))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK6)) & l1_orders_2(sK5) & ~v2_struct_0(sK5)) & l1_orders_2(sK4) & ~v2_struct_0(sK4)),
% 3.33/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f63,f81,f80,f79])).
% 3.33/1.01  
% 3.33/1.01  fof(f126,plain,(
% 3.33/1.01    v1_funct_1(sK6)),
% 3.33/1.01    inference(cnf_transformation,[],[f82])).
% 3.33/1.01  
% 3.33/1.01  fof(f19,axiom,(
% 3.33/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f52,plain,(
% 3.33/1.01    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.33/1.01    inference(ennf_transformation,[],[f19])).
% 3.33/1.01  
% 3.33/1.01  fof(f53,plain,(
% 3.33/1.01    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.33/1.01    inference(flattening,[],[f52])).
% 3.33/1.01  
% 3.33/1.01  fof(f109,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f53])).
% 3.33/1.01  
% 3.33/1.01  fof(f3,axiom,(
% 3.33/1.01    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f66,plain,(
% 3.33/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.33/1.01    inference(nnf_transformation,[],[f3])).
% 3.33/1.01  
% 3.33/1.01  fof(f67,plain,(
% 3.33/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.33/1.01    inference(rectify,[],[f66])).
% 3.33/1.01  
% 3.33/1.01  fof(f68,plain,(
% 3.33/1.01    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f69,plain,(
% 3.33/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.33/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f67,f68])).
% 3.33/1.01  
% 3.33/1.01  fof(f89,plain,(
% 3.33/1.01    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f69])).
% 3.33/1.01  
% 3.33/1.01  fof(f4,axiom,(
% 3.33/1.01    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f91,plain,(
% 3.33/1.01    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.33/1.01    inference(cnf_transformation,[],[f4])).
% 3.33/1.01  
% 3.33/1.01  fof(f22,axiom,(
% 3.33/1.01    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f28,plain,(
% 3.33/1.01    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 3.33/1.01    inference(rectify,[],[f22])).
% 3.33/1.01  
% 3.33/1.01  fof(f57,plain,(
% 3.33/1.01    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 3.33/1.01    inference(ennf_transformation,[],[f28])).
% 3.33/1.01  
% 3.33/1.01  fof(f73,plain,(
% 3.33/1.01    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)))),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f74,plain,(
% 3.33/1.01    ! [X0] : (((r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 3.33/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f57,f73])).
% 3.33/1.01  
% 3.33/1.01  fof(f113,plain,(
% 3.33/1.01    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 3.33/1.01    inference(cnf_transformation,[],[f74])).
% 3.33/1.01  
% 3.33/1.01  fof(f88,plain,(
% 3.33/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.33/1.01    inference(cnf_transformation,[],[f69])).
% 3.33/1.01  
% 3.33/1.01  fof(f132,plain,(
% 3.33/1.01    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.33/1.01    inference(equality_resolution,[],[f88])).
% 3.33/1.01  
% 3.33/1.01  fof(f90,plain,(
% 3.33/1.01    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | ~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f69])).
% 3.33/1.01  
% 3.33/1.01  fof(f87,plain,(
% 3.33/1.01    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.33/1.01    inference(cnf_transformation,[],[f69])).
% 3.33/1.01  
% 3.33/1.01  fof(f133,plain,(
% 3.33/1.01    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.33/1.01    inference(equality_resolution,[],[f87])).
% 3.33/1.01  
% 3.33/1.01  fof(f1,axiom,(
% 3.33/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f64,plain,(
% 3.33/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.33/1.01    inference(nnf_transformation,[],[f1])).
% 3.33/1.01  
% 3.33/1.01  fof(f65,plain,(
% 3.33/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.33/1.01    inference(flattening,[],[f64])).
% 3.33/1.01  
% 3.33/1.01  fof(f85,plain,(
% 3.33/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f65])).
% 3.33/1.01  
% 3.33/1.01  fof(f5,axiom,(
% 3.33/1.01    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f70,plain,(
% 3.33/1.01    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f71,plain,(
% 3.33/1.01    ! [X0] : (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 3.33/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f70])).
% 3.33/1.01  
% 3.33/1.01  fof(f93,plain,(
% 3.33/1.01    ( ! [X0] : (v1_xboole_0(sK1(X0))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f71])).
% 3.33/1.01  
% 3.33/1.01  fof(f2,axiom,(
% 3.33/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f35,plain,(
% 3.33/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.33/1.01    inference(ennf_transformation,[],[f2])).
% 3.33/1.01  
% 3.33/1.01  fof(f86,plain,(
% 3.33/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f35])).
% 3.33/1.01  
% 3.33/1.01  fof(f92,plain,(
% 3.33/1.01    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f71])).
% 3.33/1.01  
% 3.33/1.01  fof(f7,axiom,(
% 3.33/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f37,plain,(
% 3.33/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.33/1.01    inference(ennf_transformation,[],[f7])).
% 3.33/1.01  
% 3.33/1.01  fof(f38,plain,(
% 3.33/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(flattening,[],[f37])).
% 3.33/1.01  
% 3.33/1.01  fof(f95,plain,(
% 3.33/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f38])).
% 3.33/1.01  
% 3.33/1.01  fof(f6,axiom,(
% 3.33/1.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f36,plain,(
% 3.33/1.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.33/1.01    inference(ennf_transformation,[],[f6])).
% 3.33/1.01  
% 3.33/1.01  fof(f94,plain,(
% 3.33/1.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f36])).
% 3.33/1.01  
% 3.33/1.01  fof(f12,axiom,(
% 3.33/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f42,plain,(
% 3.33/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.01    inference(ennf_transformation,[],[f12])).
% 3.33/1.01  
% 3.33/1.01  fof(f99,plain,(
% 3.33/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f42])).
% 3.33/1.01  
% 3.33/1.01  fof(f14,axiom,(
% 3.33/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f45,plain,(
% 3.33/1.01    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.33/1.01    inference(ennf_transformation,[],[f14])).
% 3.33/1.01  
% 3.33/1.01  fof(f102,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f45])).
% 3.33/1.01  
% 3.33/1.01  fof(f105,plain,(
% 3.33/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f72])).
% 3.33/1.01  
% 3.33/1.01  fof(f127,plain,(
% 3.33/1.01    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))),
% 3.33/1.01    inference(cnf_transformation,[],[f82])).
% 3.33/1.01  
% 3.33/1.01  fof(f17,axiom,(
% 3.33/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f50,plain,(
% 3.33/1.01    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.33/1.01    inference(ennf_transformation,[],[f17])).
% 3.33/1.01  
% 3.33/1.01  fof(f51,plain,(
% 3.33/1.01    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.33/1.01    inference(flattening,[],[f50])).
% 3.33/1.01  
% 3.33/1.01  fof(f107,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f51])).
% 3.33/1.01  
% 3.33/1.01  fof(f128,plain,(
% 3.33/1.01    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 3.33/1.01    inference(cnf_transformation,[],[f82])).
% 3.33/1.01  
% 3.33/1.01  fof(f23,axiom,(
% 3.33/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f58,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.33/1.01    inference(ennf_transformation,[],[f23])).
% 3.33/1.01  
% 3.33/1.01  fof(f75,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.33/1.01    inference(nnf_transformation,[],[f58])).
% 3.33/1.01  
% 3.33/1.01  fof(f76,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 3.33/1.01    inference(flattening,[],[f75])).
% 3.33/1.01  
% 3.33/1.01  fof(f116,plain,(
% 3.33/1.01    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f76])).
% 3.33/1.01  
% 3.33/1.01  fof(f24,axiom,(
% 3.33/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => l1_orders_2(X1)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f59,plain,(
% 3.33/1.01    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 3.33/1.01    inference(ennf_transformation,[],[f24])).
% 3.33/1.01  
% 3.33/1.01  fof(f119,plain,(
% 3.33/1.01    ( ! [X0,X1] : (l1_orders_2(X1) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f59])).
% 3.33/1.01  
% 3.33/1.01  fof(f25,axiom,(
% 3.33/1.01    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_yellow_0(X1,X0) & v1_orders_2(X1) & ~v2_struct_0(X1) & m1_yellow_0(X1,X0)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f30,plain,(
% 3.33/1.01    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ? [X1] : (v1_orders_2(X1) & ~v2_struct_0(X1) & m1_yellow_0(X1,X0)))),
% 3.33/1.01    inference(pure_predicate_removal,[],[f25])).
% 3.33/1.01  
% 3.33/1.01  fof(f31,plain,(
% 3.33/1.01    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v2_struct_0(X1) & m1_yellow_0(X1,X0)))),
% 3.33/1.01    inference(pure_predicate_removal,[],[f30])).
% 3.33/1.01  
% 3.33/1.01  fof(f60,plain,(
% 3.33/1.01    ! [X0] : (? [X1] : (~v2_struct_0(X1) & m1_yellow_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f31])).
% 3.33/1.01  
% 3.33/1.01  fof(f61,plain,(
% 3.33/1.01    ! [X0] : (? [X1] : (~v2_struct_0(X1) & m1_yellow_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.33/1.01    inference(flattening,[],[f60])).
% 3.33/1.01  
% 3.33/1.01  fof(f77,plain,(
% 3.33/1.01    ! [X0] : (? [X1] : (~v2_struct_0(X1) & m1_yellow_0(X1,X0)) => (~v2_struct_0(sK3(X0)) & m1_yellow_0(sK3(X0),X0)))),
% 3.33/1.01    introduced(choice_axiom,[])).
% 3.33/1.01  
% 3.33/1.01  fof(f78,plain,(
% 3.33/1.01    ! [X0] : ((~v2_struct_0(sK3(X0)) & m1_yellow_0(sK3(X0),X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 3.33/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f61,f77])).
% 3.33/1.01  
% 3.33/1.01  fof(f120,plain,(
% 3.33/1.01    ( ! [X0] : (m1_yellow_0(sK3(X0),X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f78])).
% 3.33/1.01  
% 3.33/1.01  fof(f124,plain,(
% 3.33/1.01    ~v2_struct_0(sK5)),
% 3.33/1.01    inference(cnf_transformation,[],[f82])).
% 3.33/1.01  
% 3.33/1.01  fof(f125,plain,(
% 3.33/1.01    l1_orders_2(sK5)),
% 3.33/1.01    inference(cnf_transformation,[],[f82])).
% 3.33/1.01  
% 3.33/1.01  fof(f121,plain,(
% 3.33/1.01    ( ! [X0] : (~v2_struct_0(sK3(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f78])).
% 3.33/1.01  
% 3.33/1.01  fof(f21,axiom,(
% 3.33/1.01    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f56,plain,(
% 3.33/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.33/1.01    inference(ennf_transformation,[],[f21])).
% 3.33/1.01  
% 3.33/1.01  fof(f112,plain,(
% 3.33/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f56])).
% 3.33/1.01  
% 3.33/1.01  fof(f20,axiom,(
% 3.33/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f54,plain,(
% 3.33/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.33/1.01    inference(ennf_transformation,[],[f20])).
% 3.33/1.01  
% 3.33/1.01  fof(f55,plain,(
% 3.33/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.33/1.01    inference(flattening,[],[f54])).
% 3.33/1.01  
% 3.33/1.01  fof(f111,plain,(
% 3.33/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f55])).
% 3.33/1.01  
% 3.33/1.01  fof(f122,plain,(
% 3.33/1.01    ~v2_struct_0(sK4)),
% 3.33/1.01    inference(cnf_transformation,[],[f82])).
% 3.33/1.01  
% 3.33/1.01  fof(f123,plain,(
% 3.33/1.01    l1_orders_2(sK4)),
% 3.33/1.01    inference(cnf_transformation,[],[f82])).
% 3.33/1.01  
% 3.33/1.01  fof(f84,plain,(
% 3.33/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.33/1.01    inference(cnf_transformation,[],[f65])).
% 3.33/1.01  
% 3.33/1.01  fof(f130,plain,(
% 3.33/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.33/1.01    inference(equality_resolution,[],[f84])).
% 3.33/1.01  
% 3.33/1.01  fof(f13,axiom,(
% 3.33/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f43,plain,(
% 3.33/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.33/1.01    inference(ennf_transformation,[],[f13])).
% 3.33/1.01  
% 3.33/1.01  fof(f44,plain,(
% 3.33/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.33/1.01    inference(flattening,[],[f43])).
% 3.33/1.01  
% 3.33/1.01  fof(f100,plain,(
% 3.33/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f44])).
% 3.33/1.01  
% 3.33/1.01  fof(f101,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f45])).
% 3.33/1.01  
% 3.33/1.01  fof(f11,axiom,(
% 3.33/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.33/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.01  
% 3.33/1.01  fof(f41,plain,(
% 3.33/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.33/1.01    inference(ennf_transformation,[],[f11])).
% 3.33/1.01  
% 3.33/1.01  fof(f98,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.33/1.01    inference(cnf_transformation,[],[f41])).
% 3.33/1.01  
% 3.33/1.01  fof(f129,plain,(
% 3.33/1.01    k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) | ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_funct_1(sK6))),
% 3.33/1.01    inference(cnf_transformation,[],[f82])).
% 3.33/1.01  
% 3.33/1.01  fof(f117,plain,(
% 3.33/1.01    ( ! [X0,X1] : (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f76])).
% 3.33/1.01  
% 3.33/1.01  fof(f108,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f51])).
% 3.33/1.01  
% 3.33/1.01  fof(f135,plain,(
% 3.33/1.01    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 3.33/1.01    inference(equality_resolution,[],[f108])).
% 3.33/1.01  
% 3.33/1.01  fof(f115,plain,(
% 3.33/1.01    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = k3_tarski(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f74])).
% 3.33/1.01  
% 3.33/1.01  fof(f110,plain,(
% 3.33/1.01    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f53])).
% 3.33/1.01  
% 3.33/1.01  fof(f136,plain,(
% 3.33/1.01    ( ! [X2,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 3.33/1.01    inference(equality_resolution,[],[f110])).
% 3.33/1.01  
% 3.33/1.01  fof(f114,plain,(
% 3.33/1.01    ( ! [X0] : (k1_xboole_0 != sK2(X0) | k1_xboole_0 = k3_tarski(X0)) )),
% 3.33/1.01    inference(cnf_transformation,[],[f74])).
% 3.33/1.01  
% 3.33/1.01  cnf(c_14,plain,
% 3.33/1.01      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.33/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_22,plain,
% 3.33/1.01      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.33/1.01      | ~ v4_relat_1(X0,k1_relat_1(X0))
% 3.33/1.01      | ~ v1_relat_1(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f134]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_691,plain,
% 3.33/1.01      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.33/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.33/1.01      | ~ v1_relat_1(X0)
% 3.33/1.01      | X0 != X1
% 3.33/1.01      | k1_relat_1(X0) != X2 ),
% 3.33/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_692,plain,
% 3.33/1.01      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.33/1.01      | ~ v1_relat_1(X0) ),
% 3.33/1.01      inference(unflattening,[status(thm)],[c_691]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_13,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_702,plain,
% 3.33/1.01      ( v1_partfun1(X0,k1_relat_1(X0))
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ),
% 3.33/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_692,c_13]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_20,plain,
% 3.33/1.01      ( v1_funct_2(X0,X1,X2)
% 3.33/1.01      | ~ v1_partfun1(X0,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | ~ v1_funct_1(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f104]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_42,negated_conjecture,
% 3.33/1.01      ( v1_funct_1(sK6) ),
% 3.33/1.01      inference(cnf_transformation,[],[f126]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_797,plain,
% 3.33/1.01      ( v1_funct_2(X0,X1,X2)
% 3.33/1.01      | ~ v1_partfun1(X0,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | sK6 != X0 ),
% 3.33/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_42]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_798,plain,
% 3.33/1.01      ( v1_funct_2(sK6,X0,X1)
% 3.33/1.01      | ~ v1_partfun1(sK6,X0)
% 3.33/1.01      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.33/1.01      inference(unflattening,[status(thm)],[c_797]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_27,plain,
% 3.33/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | ~ v1_funct_1(X0)
% 3.33/1.01      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.33/1.01      | k1_xboole_0 = X2 ),
% 3.33/1.01      inference(cnf_transformation,[],[f109]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_731,plain,
% 3.33/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.33/1.01      | sK6 != X0
% 3.33/1.01      | k1_xboole_0 = X2 ),
% 3.33/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_42]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_732,plain,
% 3.33/1.01      ( ~ v1_funct_2(sK6,X0,X1)
% 3.33/1.01      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.01      | k8_relset_1(X0,X1,sK6,X1) = X0
% 3.33/1.01      | k1_xboole_0 = X1 ),
% 3.33/1.01      inference(unflattening,[status(thm)],[c_731]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1140,plain,
% 3.33/1.01      ( ~ v1_partfun1(sK6,X0)
% 3.33/1.01      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.01      | k8_relset_1(X0,X1,sK6,X1) = X0
% 3.33/1.01      | k1_xboole_0 = X1 ),
% 3.33/1.01      inference(resolution,[status(thm)],[c_798,c_732]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1344,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.33/1.01      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.33/1.01      | k8_relset_1(X2,X3,sK6,X3) = X2
% 3.33/1.01      | k1_relat_1(X0) != X2
% 3.33/1.01      | sK6 != X0
% 3.33/1.01      | k1_xboole_0 = X3 ),
% 3.33/1.01      inference(resolution_lifted,[status(thm)],[c_702,c_1140]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1345,plain,
% 3.33/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)))
% 3.33/1.01      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X1)))
% 3.33/1.01      | k8_relset_1(k1_relat_1(sK6),X1,sK6,X1) = k1_relat_1(sK6)
% 3.33/1.01      | k1_xboole_0 = X1 ),
% 3.33/1.01      inference(unflattening,[status(thm)],[c_1344]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2021,plain,
% 3.33/1.01      ( sP2_iProver_split | sP1_iProver_split ),
% 3.33/1.01      inference(splitting,
% 3.33/1.01                [splitting(split),new_symbols(definition,[])],
% 3.33/1.01                [c_1345]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_544,plain,
% 3.33/1.01      ( ~ m1_yellow_0(X0,X1) | m1_yellow_0(X2,X1) | X2 != X0 ),
% 3.33/1.01      theory(equality) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_540,plain,
% 3.33/1.01      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.33/1.01      theory(equality) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_539,plain,
% 3.33/1.01      ( ~ v1_partfun1(X0,X1) | v1_partfun1(X0,X2) | X2 != X1 ),
% 3.33/1.01      theory(equality) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_538,plain,
% 3.33/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.33/1.01      | v1_funct_2(X3,X4,X5)
% 3.33/1.01      | X3 != X0
% 3.33/1.01      | X4 != X1
% 3.33/1.01      | X5 != X2 ),
% 3.33/1.01      theory(equality) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_534,plain,
% 3.33/1.01      ( ~ v4_relat_1(X0,X1) | v4_relat_1(X0,X2) | X2 != X1 ),
% 3.33/1.01      theory(equality) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2027,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5,plain,
% 3.33/1.01      ( r2_hidden(sK0(X0,X1),X1)
% 3.33/1.01      | r1_tarski(sK0(X0,X1),X0)
% 3.33/1.01      | k1_zfmisc_1(X0) = X1 ),
% 3.33/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3081,plain,
% 3.33/1.01      ( k1_zfmisc_1(X0) = X1
% 3.33/1.01      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.33/1.01      | r1_tarski(sK0(X0,X1),X0) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_8,plain,
% 3.33/1.01      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.33/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_32,plain,
% 3.33/1.01      ( ~ r2_hidden(X0,X1) | k3_tarski(X1) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.33/1.01      inference(cnf_transformation,[],[f113]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3068,plain,
% 3.33/1.01      ( k3_tarski(X0) != k1_xboole_0
% 3.33/1.01      | k1_xboole_0 = X1
% 3.33/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5212,plain,
% 3.33/1.01      ( k1_xboole_0 != X0
% 3.33/1.01      | k1_xboole_0 = X1
% 3.33/1.01      | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_8,c_3068]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5218,plain,
% 3.33/1.01      ( k1_xboole_0 = X0
% 3.33/1.01      | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.33/1.01      inference(equality_resolution,[status(thm)],[c_5212]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5864,plain,
% 3.33/1.01      ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
% 3.33/1.01      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 3.33/1.01      | r1_tarski(sK0(X0,k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3081,c_5218]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6,plain,
% 3.33/1.01      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.33/1.01      inference(cnf_transformation,[],[f132]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3080,plain,
% 3.33/1.01      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.33/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4,plain,
% 3.33/1.01      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.33/1.01      | ~ r1_tarski(sK0(X0,X1),X0)
% 3.33/1.01      | k1_zfmisc_1(X0) = X1 ),
% 3.33/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3082,plain,
% 3.33/1.01      ( k1_zfmisc_1(X0) = X1
% 3.33/1.01      | r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.33/1.01      | r1_tarski(sK0(X0,X1),X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5904,plain,
% 3.33/1.01      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 3.33/1.01      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) != iProver_top
% 3.33/1.01      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3080,c_3082]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_9070,plain,
% 3.33/1.01      ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
% 3.33/1.01      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 3.33/1.01      | r1_tarski(sK0(X0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_5864,c_5904]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_7,plain,
% 3.33/1.01      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.33/1.01      inference(cnf_transformation,[],[f133]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3079,plain,
% 3.33/1.01      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.33/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5863,plain,
% 3.33/1.01      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 3.33/1.01      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) = iProver_top
% 3.33/1.01      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3081,c_3079]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_0,plain,
% 3.33/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.33/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3085,plain,
% 3.33/1.01      ( X0 = X1
% 3.33/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.33/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_9040,plain,
% 3.33/1.01      ( sK0(X0,k1_zfmisc_1(X1)) = X0
% 3.33/1.01      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 3.33/1.01      | r1_tarski(X0,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
% 3.33/1.01      | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_5863,c_3085]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_9037,plain,
% 3.33/1.01      ( sK0(X0,k1_zfmisc_1(X1)) = X1
% 3.33/1.01      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 3.33/1.01      | r1_tarski(X1,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
% 3.33/1.01      | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_5863,c_3085]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5469,plain,
% 3.33/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3080,c_5218]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5862,plain,
% 3.33/1.01      ( sK0(k1_xboole_0,X0) = k1_xboole_0
% 3.33/1.01      | k1_zfmisc_1(k1_xboole_0) = X0
% 3.33/1.01      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3081,c_5469]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_7671,plain,
% 3.33/1.01      ( sK0(k1_xboole_0,k1_zfmisc_1(X0)) = k1_xboole_0
% 3.33/1.01      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 3.33/1.01      | r1_tarski(sK0(k1_xboole_0,k1_zfmisc_1(X0)),X0) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_5862,c_3079]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_8873,plain,
% 3.33/1.01      ( sK0(k1_xboole_0,k1_zfmisc_1(X0)) = X0
% 3.33/1.01      | sK0(k1_xboole_0,k1_zfmisc_1(X0)) = k1_xboole_0
% 3.33/1.01      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 3.33/1.01      | r1_tarski(X0,sK0(k1_xboole_0,k1_zfmisc_1(X0))) != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_7671,c_3085]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_9,plain,
% 3.33/1.01      ( v1_xboole_0(sK1(X0)) ),
% 3.33/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3078,plain,
% 3.33/1.01      ( v1_xboole_0(sK1(X0)) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3,plain,
% 3.33/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.33/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3083,plain,
% 3.33/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4188,plain,
% 3.33/1.01      ( sK1(X0) = k1_xboole_0 ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3078,c_3083]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_10,plain,
% 3.33/1.01      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
% 3.33/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3077,plain,
% 3.33/1.01      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_4863,plain,
% 3.33/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.33/1.01      inference(demodulation,[status(thm)],[c_4188,c_3077]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_12,plain,
% 3.33/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.33/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_674,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | ~ v1_relat_1(X0)
% 3.33/1.01      | k7_relat_1(X0,X1) = X0 ),
% 3.33/1.01      inference(resolution,[status(thm)],[c_14,c_12]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_678,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | k7_relat_1(X0,X1) = X0 ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_674,c_14,c_13,c_12]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3060,plain,
% 3.33/1.01      ( k7_relat_1(X0,X1) = X0
% 3.33/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5680,plain,
% 3.33/1.01      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_4863,c_3060]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3075,plain,
% 3.33/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.33/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5014,plain,
% 3.33/1.01      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_4863,c_3075]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_11,plain,
% 3.33/1.01      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.33/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3076,plain,
% 3.33/1.01      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.33/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5128,plain,
% 3.33/1.01      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_5014,c_3076]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_8701,plain,
% 3.33/1.01      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 3.33/1.01      inference(demodulation,[status(thm)],[c_5680,c_5128]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_16,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.33/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3073,plain,
% 3.33/1.01      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.33/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5801,plain,
% 3.33/1.01      ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_4863,c_3073]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_8705,plain,
% 3.33/1.01      ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k2_relat_1(k1_xboole_0) ),
% 3.33/1.01      inference(demodulation,[status(thm)],[c_8701,c_5801]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_18,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f102]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3071,plain,
% 3.33/1.01      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
% 3.33/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6564,plain,
% 3.33/1.01      ( k8_relset_1(X0,X1,k1_xboole_0,k7_relset_1(X0,X1,k1_xboole_0,X0)) = k1_relset_1(X0,X1,k1_xboole_0) ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_4863,c_3071]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6963,plain,
% 3.33/1.01      ( k8_relset_1(X0,X1,k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) = k1_relset_1(X0,X1,k1_xboole_0) ),
% 3.33/1.01      inference(demodulation,[status(thm)],[c_6564,c_5801]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_8704,plain,
% 3.33/1.01      ( k8_relset_1(X0,X1,k1_xboole_0,k2_relat_1(k1_xboole_0)) = k1_relset_1(X0,X1,k1_xboole_0) ),
% 3.33/1.01      inference(demodulation,[status(thm)],[c_8701,c_6963]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_23,plain,
% 3.33/1.01      ( ~ v1_partfun1(X0,X1)
% 3.33/1.01      | ~ v4_relat_1(X0,X1)
% 3.33/1.01      | ~ v1_relat_1(X0)
% 3.33/1.01      | k1_relat_1(X0) = X1 ),
% 3.33/1.01      inference(cnf_transformation,[],[f105]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_654,plain,
% 3.33/1.01      ( ~ v1_partfun1(X0,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | ~ v1_relat_1(X0)
% 3.33/1.01      | k1_relat_1(X0) = X1 ),
% 3.33/1.01      inference(resolution,[status(thm)],[c_14,c_23]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_658,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | ~ v1_partfun1(X0,X1)
% 3.33/1.01      | k1_relat_1(X0) = X1 ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_654,c_23,c_14,c_13]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_659,plain,
% 3.33/1.01      ( ~ v1_partfun1(X0,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | k1_relat_1(X0) = X1 ),
% 3.33/1.01      inference(renaming,[status(thm)],[c_658]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_41,negated_conjecture,
% 3.33/1.01      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
% 3.33/1.01      inference(cnf_transformation,[],[f127]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_25,plain,
% 3.33/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.33/1.01      | v1_partfun1(X0,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | ~ v1_funct_1(X0)
% 3.33/1.01      | k1_xboole_0 = X2 ),
% 3.33/1.01      inference(cnf_transformation,[],[f107]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_764,plain,
% 3.33/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.33/1.01      | v1_partfun1(X0,X1)
% 3.33/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | sK6 != X0
% 3.33/1.01      | k1_xboole_0 = X2 ),
% 3.33/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_42]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_765,plain,
% 3.33/1.01      ( ~ v1_funct_2(sK6,X0,X1)
% 3.33/1.01      | v1_partfun1(sK6,X0)
% 3.33/1.01      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.01      | k1_xboole_0 = X1 ),
% 3.33/1.01      inference(unflattening,[status(thm)],[c_764]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1191,plain,
% 3.33/1.01      ( v1_partfun1(sK6,X0)
% 3.33/1.01      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.01      | u1_struct_0(sK5) != X1
% 3.33/1.01      | u1_struct_0(sK4) != X0
% 3.33/1.01      | sK6 != sK6
% 3.33/1.01      | k1_xboole_0 = X1 ),
% 3.33/1.01      inference(resolution_lifted,[status(thm)],[c_41,c_765]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1192,plain,
% 3.33/1.01      ( v1_partfun1(sK6,u1_struct_0(sK4))
% 3.33/1.01      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 3.33/1.01      | k1_xboole_0 = u1_struct_0(sK5) ),
% 3.33/1.01      inference(unflattening,[status(thm)],[c_1191]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_40,negated_conjecture,
% 3.33/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
% 3.33/1.01      inference(cnf_transformation,[],[f128]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1194,plain,
% 3.33/1.01      ( v1_partfun1(sK6,u1_struct_0(sK4)) | k1_xboole_0 = u1_struct_0(sK5) ),
% 3.33/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1192,c_40]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1329,plain,
% 3.33/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.01      | u1_struct_0(sK5) = k1_xboole_0
% 3.33/1.01      | u1_struct_0(sK4) != X1
% 3.33/1.01      | k1_relat_1(X0) = X1
% 3.33/1.01      | sK6 != X0 ),
% 3.33/1.01      inference(resolution_lifted,[status(thm)],[c_659,c_1194]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1330,plain,
% 3.33/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0)))
% 3.33/1.01      | u1_struct_0(sK5) = k1_xboole_0
% 3.33/1.01      | k1_relat_1(sK6) = u1_struct_0(sK4) ),
% 3.33/1.01      inference(unflattening,[status(thm)],[c_1329]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2023,plain,
% 3.33/1.01      ( sP3_iProver_split
% 3.33/1.01      | u1_struct_0(sK5) = k1_xboole_0
% 3.33/1.01      | k1_relat_1(sK6) = u1_struct_0(sK4) ),
% 3.33/1.01      inference(splitting,
% 3.33/1.01                [splitting(split),new_symbols(definition,[])],
% 3.33/1.01                [c_1330]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3049,plain,
% 3.33/1.01      ( u1_struct_0(sK5) = k1_xboole_0
% 3.33/1.01      | k1_relat_1(sK6) = u1_struct_0(sK4)
% 3.33/1.01      | sP3_iProver_split = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_2023]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3066,plain,
% 3.33/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2022,plain,
% 3.33/1.01      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0)))
% 3.33/1.01      | ~ sP3_iProver_split ),
% 3.33/1.01      inference(splitting,
% 3.33/1.01                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 3.33/1.01                [c_1330]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3050,plain,
% 3.33/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) != iProver_top
% 3.33/1.01      | sP3_iProver_split != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_2022]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3637,plain,
% 3.33/1.01      ( sP3_iProver_split != iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3066,c_3050]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3638,plain,
% 3.33/1.01      ( ~ sP3_iProver_split ),
% 3.33/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3637]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3861,plain,
% 3.33/1.01      ( k1_relat_1(sK6) = u1_struct_0(sK4) | u1_struct_0(sK5) = k1_xboole_0 ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_3049,c_2023,c_3638]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3862,plain,
% 3.33/1.01      ( u1_struct_0(sK5) = k1_xboole_0 | k1_relat_1(sK6) = u1_struct_0(sK4) ),
% 3.33/1.01      inference(renaming,[status(thm)],[c_3861]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_35,plain,
% 3.33/1.01      ( ~ m1_yellow_0(X0,X1)
% 3.33/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.33/1.01      | ~ l1_orders_2(X1)
% 3.33/1.01      | ~ l1_orders_2(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f116]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_36,plain,
% 3.33/1.01      ( ~ m1_yellow_0(X0,X1) | ~ l1_orders_2(X1) | l1_orders_2(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f119]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_262,plain,
% 3.33/1.01      ( ~ l1_orders_2(X1)
% 3.33/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.33/1.01      | ~ m1_yellow_0(X0,X1) ),
% 3.33/1.01      inference(global_propositional_subsumption,[status(thm)],[c_35,c_36]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_263,plain,
% 3.33/1.01      ( ~ m1_yellow_0(X0,X1)
% 3.33/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.33/1.01      | ~ l1_orders_2(X1) ),
% 3.33/1.01      inference(renaming,[status(thm)],[c_262]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_38,plain,
% 3.33/1.01      ( m1_yellow_0(sK3(X0),X0) | ~ l1_orders_2(X0) | v2_struct_0(X0) ),
% 3.33/1.01      inference(cnf_transformation,[],[f120]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1097,plain,
% 3.33/1.01      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.33/1.01      | ~ l1_orders_2(X1)
% 3.33/1.01      | ~ l1_orders_2(X2)
% 3.33/1.01      | v2_struct_0(X2)
% 3.33/1.01      | X2 != X1
% 3.33/1.01      | sK3(X2) != X0 ),
% 3.33/1.01      inference(resolution_lifted,[status(thm)],[c_263,c_38]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1098,plain,
% 3.33/1.01      ( r1_tarski(u1_struct_0(sK3(X0)),u1_struct_0(X0))
% 3.33/1.01      | ~ l1_orders_2(X0)
% 3.33/1.01      | v2_struct_0(X0) ),
% 3.33/1.01      inference(unflattening,[status(thm)],[c_1097]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3058,plain,
% 3.33/1.01      ( r1_tarski(u1_struct_0(sK3(X0)),u1_struct_0(X0)) = iProver_top
% 3.33/1.01      | l1_orders_2(X0) != iProver_top
% 3.33/1.01      | v2_struct_0(X0) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_1098]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_5694,plain,
% 3.33/1.01      ( u1_struct_0(sK4) = k1_relat_1(sK6)
% 3.33/1.01      | r1_tarski(u1_struct_0(sK3(sK5)),k1_xboole_0) = iProver_top
% 3.33/1.01      | l1_orders_2(sK5) != iProver_top
% 3.33/1.01      | v2_struct_0(sK5) = iProver_top ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_3862,c_3058]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_44,negated_conjecture,
% 3.33/1.01      ( ~ v2_struct_0(sK5) ),
% 3.33/1.01      inference(cnf_transformation,[],[f124]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_49,plain,
% 3.33/1.01      ( v2_struct_0(sK5) != iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_43,negated_conjecture,
% 3.33/1.01      ( l1_orders_2(sK5) ),
% 3.33/1.01      inference(cnf_transformation,[],[f125]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_50,plain,
% 3.33/1.01      ( l1_orders_2(sK5) = iProver_top ),
% 3.33/1.01      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6146,plain,
% 3.33/1.01      ( u1_struct_0(sK4) = k1_relat_1(sK6)
% 3.33/1.01      | r1_tarski(u1_struct_0(sK3(sK5)),k1_xboole_0) = iProver_top ),
% 3.33/1.01      inference(global_propositional_subsumption,
% 3.33/1.01                [status(thm)],
% 3.33/1.01                [c_5694,c_49,c_50]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_6153,plain,
% 3.33/1.01      ( u1_struct_0(sK3(sK5)) = k1_xboole_0
% 3.33/1.01      | u1_struct_0(sK4) = k1_relat_1(sK6) ),
% 3.33/1.01      inference(superposition,[status(thm)],[c_6146,c_5469]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_135,plain,
% 3.33/1.01      ( v1_xboole_0(sK1(k1_xboole_0)) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_589,plain,
% 3.33/1.01      ( sK1(X0) != X1 | k1_xboole_0 = X1 ),
% 3.33/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_9]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_590,plain,
% 3.33/1.01      ( k1_xboole_0 = sK1(X0) ),
% 3.33/1.01      inference(unflattening,[status(thm)],[c_589]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_591,plain,
% 3.33/1.01      ( k1_xboole_0 = sK1(k1_xboole_0) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_590]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_37,plain,
% 3.33/1.01      ( ~ l1_orders_2(X0) | v2_struct_0(X0) | ~ v2_struct_0(sK3(X0)) ),
% 3.33/1.01      inference(cnf_transformation,[],[f121]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3429,plain,
% 3.33/1.01      ( ~ l1_orders_2(sK5) | ~ v2_struct_0(sK3(sK5)) | v2_struct_0(sK5) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_37]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1112,plain,
% 3.33/1.01      ( ~ l1_orders_2(X0)
% 3.33/1.01      | ~ l1_orders_2(X1)
% 3.33/1.01      | l1_orders_2(X2)
% 3.33/1.01      | v2_struct_0(X1)
% 3.33/1.01      | X1 != X0
% 3.33/1.01      | sK3(X1) != X2 ),
% 3.33/1.01      inference(resolution_lifted,[status(thm)],[c_36,c_38]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_1113,plain,
% 3.33/1.01      ( ~ l1_orders_2(X0) | l1_orders_2(sK3(X0)) | v2_struct_0(X0) ),
% 3.33/1.01      inference(unflattening,[status(thm)],[c_1112]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3445,plain,
% 3.33/1.01      ( l1_orders_2(sK3(sK5)) | ~ l1_orders_2(sK5) | v2_struct_0(sK5) ),
% 3.33/1.01      inference(instantiation,[status(thm)],[c_1113]) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_2031,plain,
% 3.33/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.33/1.01      theory(equality) ).
% 3.33/1.01  
% 3.33/1.01  cnf(c_3523,plain,
% 3.33/1.01      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK1(X1)) | X0 != sK1(X1) ),
% 3.33/1.02      inference(instantiation,[status(thm)],[c_2031]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3525,plain,
% 3.33/1.02      ( ~ v1_xboole_0(sK1(k1_xboole_0))
% 3.33/1.02      | v1_xboole_0(k1_xboole_0)
% 3.33/1.02      | k1_xboole_0 != sK1(k1_xboole_0) ),
% 3.33/1.02      inference(instantiation,[status(thm)],[c_3523]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_29,plain,
% 3.33/1.02      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.33/1.02      inference(cnf_transformation,[],[f112]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_28,plain,
% 3.33/1.02      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.33/1.02      inference(cnf_transformation,[],[f111]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_613,plain,
% 3.33/1.02      ( ~ l1_orders_2(X0) | v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.33/1.02      inference(resolution,[status(thm)],[c_29,c_28]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3593,plain,
% 3.33/1.02      ( ~ l1_orders_2(sK3(sK5))
% 3.33/1.02      | v2_struct_0(sK3(sK5))
% 3.33/1.02      | ~ v1_xboole_0(u1_struct_0(sK3(sK5))) ),
% 3.33/1.02      inference(instantiation,[status(thm)],[c_613]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4357,plain,
% 3.33/1.02      ( ~ v1_xboole_0(X0)
% 3.33/1.02      | v1_xboole_0(u1_struct_0(sK3(sK5)))
% 3.33/1.02      | u1_struct_0(sK3(sK5)) != X0 ),
% 3.33/1.02      inference(instantiation,[status(thm)],[c_2031]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4359,plain,
% 3.33/1.02      ( v1_xboole_0(u1_struct_0(sK3(sK5)))
% 3.33/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 3.33/1.02      | u1_struct_0(sK3(sK5)) != k1_xboole_0 ),
% 3.33/1.02      inference(instantiation,[status(thm)],[c_4357]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6158,plain,
% 3.33/1.02      ( u1_struct_0(sK4) = k1_relat_1(sK6) ),
% 3.33/1.02      inference(global_propositional_subsumption,
% 3.33/1.02                [status(thm)],
% 3.33/1.02                [c_6153,c_44,c_43,c_135,c_591,c_3429,c_3445,c_3525,c_3593,
% 3.33/1.02                 c_4359]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6234,plain,
% 3.33/1.02      ( r1_tarski(u1_struct_0(sK3(sK4)),k1_relat_1(sK6)) = iProver_top
% 3.33/1.02      | l1_orders_2(sK4) != iProver_top
% 3.33/1.02      | v2_struct_0(sK4) = iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_6158,c_3058]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_46,negated_conjecture,
% 3.33/1.02      ( ~ v2_struct_0(sK4) ),
% 3.33/1.02      inference(cnf_transformation,[],[f122]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_47,plain,
% 3.33/1.02      ( v2_struct_0(sK4) != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_45,negated_conjecture,
% 3.33/1.02      ( l1_orders_2(sK4) ),
% 3.33/1.02      inference(cnf_transformation,[],[f123]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_48,plain,
% 3.33/1.02      ( l1_orders_2(sK4) = iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_8436,plain,
% 3.33/1.02      ( r1_tarski(u1_struct_0(sK3(sK4)),k1_relat_1(sK6)) = iProver_top ),
% 3.33/1.02      inference(global_propositional_subsumption,
% 3.33/1.02                [status(thm)],
% 3.33/1.02                [c_6234,c_47,c_48]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_8441,plain,
% 3.33/1.02      ( u1_struct_0(sK3(sK4)) = k1_relat_1(sK6)
% 3.33/1.02      | r1_tarski(k1_relat_1(sK6),u1_struct_0(sK3(sK4))) != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_8436,c_3085]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f130]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3084,plain,
% 3.33/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6178,plain,
% 3.33/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK5)))) = iProver_top ),
% 3.33/1.02      inference(demodulation,[status(thm)],[c_6158,c_3066]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_17,plain,
% 3.33/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.33/1.02      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 3.33/1.02      inference(cnf_transformation,[],[f100]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3072,plain,
% 3.33/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.33/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 3.33/1.02      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6576,plain,
% 3.33/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) = iProver_top
% 3.33/1.02      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_6178,c_3072]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_19,plain,
% 3.33/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.02      | k7_relset_1(X1,X2,X0,k8_relset_1(X1,X2,X0,X2)) = k2_relset_1(X1,X2,X0) ),
% 3.33/1.02      inference(cnf_transformation,[],[f101]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3070,plain,
% 3.33/1.02      ( k7_relset_1(X0,X1,X2,k8_relset_1(X0,X1,X2,X1)) = k2_relset_1(X0,X1,X2)
% 3.33/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6802,plain,
% 3.33/1.02      ( k7_relset_1(k1_relat_1(sK6),X0,sK6,k8_relset_1(k1_relat_1(sK6),X0,sK6,X0)) = k2_relset_1(k1_relat_1(sK6),X0,sK6)
% 3.33/1.02      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_6576,c_3070]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_7276,plain,
% 3.33/1.02      ( k7_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k2_relat_1(sK6))) = k2_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3084,c_6802]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_15,plain,
% 3.33/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.33/1.02      inference(cnf_transformation,[],[f98]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3074,plain,
% 3.33/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.33/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6804,plain,
% 3.33/1.02      ( k2_relset_1(k1_relat_1(sK6),X0,sK6) = k2_relat_1(sK6)
% 3.33/1.02      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_6576,c_3074]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6969,plain,
% 3.33/1.02      ( k2_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) = k2_relat_1(sK6) ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3084,c_6804]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_7277,plain,
% 3.33/1.02      ( k7_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k2_relat_1(sK6))) = k2_relat_1(sK6) ),
% 3.33/1.02      inference(light_normalisation,[status(thm)],[c_7276,c_6969]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6801,plain,
% 3.33/1.02      ( k8_relset_1(k1_relat_1(sK6),X0,sK6,k7_relset_1(k1_relat_1(sK6),X0,sK6,k1_relat_1(sK6))) = k1_relset_1(k1_relat_1(sK6),X0,sK6)
% 3.33/1.02      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_6576,c_3071]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_7281,plain,
% 3.33/1.02      ( k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k7_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k1_relat_1(sK6))) = k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3084,c_6801]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6803,plain,
% 3.33/1.02      ( k7_relset_1(k1_relat_1(sK6),X0,sK6,X1) = k9_relat_1(sK6,X1)
% 3.33/1.02      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_6576,c_3073]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_7142,plain,
% 3.33/1.02      ( k7_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,X0) = k9_relat_1(sK6,X0) ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3084,c_6803]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_7483,plain,
% 3.33/1.02      ( k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k9_relat_1(sK6,k1_relat_1(sK6))) = k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) ),
% 3.33/1.02      inference(demodulation,[status(thm)],[c_7281,c_7142]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_5678,plain,
% 3.33/1.02      ( k7_relat_1(sK6,u1_struct_0(sK4)) = sK6 ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3066,c_3060]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4721,plain,
% 3.33/1.02      ( v1_relat_1(sK6) = iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3066,c_3075]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4796,plain,
% 3.33/1.02      ( k2_relat_1(k7_relat_1(sK6,X0)) = k9_relat_1(sK6,X0) ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_4721,c_3076]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_5930,plain,
% 3.33/1.02      ( k9_relat_1(sK6,u1_struct_0(sK4)) = k2_relat_1(sK6) ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_5678,c_4796]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6162,plain,
% 3.33/1.02      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
% 3.33/1.02      inference(demodulation,[status(thm)],[c_6158,c_5930]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_7484,plain,
% 3.33/1.02      ( k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k2_relat_1(sK6)) = k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) ),
% 3.33/1.02      inference(light_normalisation,[status(thm)],[c_7483,c_6162]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_8174,plain,
% 3.33/1.02      ( k7_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6)) = k2_relat_1(sK6) ),
% 3.33/1.02      inference(light_normalisation,[status(thm)],[c_7277,c_7484]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_8178,plain,
% 3.33/1.02      ( k9_relat_1(sK6,k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6)) = k2_relat_1(sK6) ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_8174,c_7142]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3061,plain,
% 3.33/1.02      ( l1_orders_2(X0) != iProver_top
% 3.33/1.02      | v2_struct_0(X0) = iProver_top
% 3.33/1.02      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6935,plain,
% 3.33/1.02      ( l1_orders_2(sK4) != iProver_top
% 3.33/1.02      | v2_struct_0(sK4) = iProver_top
% 3.33/1.02      | v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_6158,c_3061]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_7761,plain,
% 3.33/1.02      ( v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
% 3.33/1.02      inference(global_propositional_subsumption,
% 3.33/1.02                [status(thm)],
% 3.33/1.02                [c_6935,c_47,c_48]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_7748,plain,
% 3.33/1.02      ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = X0
% 3.33/1.02      | sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
% 3.33/1.02      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 3.33/1.02      | r1_tarski(X0,sK0(X0,k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_5864,c_3085]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_7670,plain,
% 3.33/1.02      ( sK0(k1_xboole_0,X0) = k1_xboole_0
% 3.33/1.02      | k1_zfmisc_1(k1_xboole_0) = X0
% 3.33/1.02      | r1_tarski(sK0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_5862,c_3082]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_2020,plain,
% 3.33/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)))
% 3.33/1.02      | k8_relset_1(k1_relat_1(sK6),X0,sK6,X0) = k1_relat_1(sK6)
% 3.33/1.02      | k1_xboole_0 = X0
% 3.33/1.02      | ~ sP2_iProver_split ),
% 3.33/1.02      inference(splitting,
% 3.33/1.02                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.33/1.02                [c_1345]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3048,plain,
% 3.33/1.02      ( k8_relset_1(k1_relat_1(sK6),X0,sK6,X0) = k1_relat_1(sK6)
% 3.33/1.02      | k1_xboole_0 = X0
% 3.33/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top
% 3.33/1.02      | sP2_iProver_split != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_2020]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_39,negated_conjecture,
% 3.33/1.02      ( ~ v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4))
% 3.33/1.02      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.33/1.02      | ~ v1_funct_1(k2_funct_1(sK6))
% 3.33/1.02      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 3.33/1.02      inference(cnf_transformation,[],[f129]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_812,plain,
% 3.33/1.02      ( ~ v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4))
% 3.33/1.02      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.33/1.02      | k2_funct_1(sK6) != sK6
% 3.33/1.02      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 3.33/1.02      inference(resolution_lifted,[status(thm)],[c_39,c_42]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1172,plain,
% 3.33/1.02      ( ~ v1_partfun1(sK6,X0)
% 3.33/1.02      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.02      | k2_funct_1(sK6) != sK6
% 3.33/1.02      | u1_struct_0(sK5) != X0
% 3.33/1.02      | u1_struct_0(sK4) != X1
% 3.33/1.02      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 3.33/1.02      inference(resolution_lifted,[status(thm)],[c_812,c_798]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1173,plain,
% 3.33/1.02      ( ~ v1_partfun1(sK6,u1_struct_0(sK5))
% 3.33/1.02      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.33/1.02      | k2_funct_1(sK6) != sK6
% 3.33/1.02      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 3.33/1.02      inference(unflattening,[status(thm)],[c_1172]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1380,plain,
% 3.33/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.33/1.02      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.33/1.02      | k2_funct_1(sK6) != sK6
% 3.33/1.02      | k1_relat_1(X0) != u1_struct_0(sK5)
% 3.33/1.02      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
% 3.33/1.02      | sK6 != X0 ),
% 3.33/1.02      inference(resolution_lifted,[status(thm)],[c_702,c_1173]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1381,plain,
% 3.33/1.02      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)))
% 3.33/1.02      | k2_funct_1(sK6) != sK6
% 3.33/1.02      | k1_relat_1(sK6) != u1_struct_0(sK5)
% 3.33/1.02      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 3.33/1.02      inference(unflattening,[status(thm)],[c_1380]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_2017,plain,
% 3.33/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)))
% 3.33/1.02      | ~ sP1_iProver_split ),
% 3.33/1.02      inference(splitting,
% 3.33/1.02                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.33/1.02                [c_1381]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_2071,plain,
% 3.33/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top
% 3.33/1.02      | sP1_iProver_split != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_2017]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_2077,plain,
% 3.33/1.02      ( sP2_iProver_split = iProver_top | sP1_iProver_split = iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_2021]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_2079,plain,
% 3.33/1.02      ( k8_relset_1(k1_relat_1(sK6),X0,sK6,X0) = k1_relat_1(sK6)
% 3.33/1.02      | k1_xboole_0 = X0
% 3.33/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top
% 3.33/1.02      | sP2_iProver_split != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_2020]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4662,plain,
% 3.33/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top
% 3.33/1.02      | k1_xboole_0 = X0
% 3.33/1.02      | k8_relset_1(k1_relat_1(sK6),X0,sK6,X0) = k1_relat_1(sK6) ),
% 3.33/1.02      inference(global_propositional_subsumption,
% 3.33/1.02                [status(thm)],
% 3.33/1.02                [c_3048,c_2071,c_2077,c_2079]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4663,plain,
% 3.33/1.02      ( k8_relset_1(k1_relat_1(sK6),X0,sK6,X0) = k1_relat_1(sK6)
% 3.33/1.02      | k1_xboole_0 = X0
% 3.33/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top ),
% 3.33/1.02      inference(renaming,[status(thm)],[c_4662]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6805,plain,
% 3.33/1.02      ( k8_relset_1(k1_relat_1(sK6),X0,sK6,X0) = k1_relat_1(sK6)
% 3.33/1.02      | k1_xboole_0 = X0
% 3.33/1.02      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_6576,c_4663]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_7368,plain,
% 3.33/1.02      ( k8_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6,k2_relat_1(sK6)) = k1_relat_1(sK6)
% 3.33/1.02      | k2_relat_1(sK6) = k1_xboole_0 ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3084,c_6805]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_7551,plain,
% 3.33/1.02      ( k1_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) = k1_relat_1(sK6)
% 3.33/1.02      | k2_relat_1(sK6) = k1_xboole_0 ),
% 3.33/1.02      inference(demodulation,[status(thm)],[c_7368,c_7484]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6565,plain,
% 3.33/1.02      ( k8_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,k7_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,k1_relat_1(sK6))) = k1_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6) ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_6178,c_3071]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6452,plain,
% 3.33/1.02      ( k7_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,k8_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,u1_struct_0(sK5))) = k2_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6) ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_6178,c_3070]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_5301,plain,
% 3.33/1.02      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_relat_1(sK6) ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3066,c_3074]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6166,plain,
% 3.33/1.02      ( k2_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6) = k2_relat_1(sK6) ),
% 3.33/1.02      inference(demodulation,[status(thm)],[c_6158,c_5301]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1406,plain,
% 3.33/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.02      | k8_relset_1(X0,X1,sK6,X1) = X0
% 3.33/1.02      | u1_struct_0(sK5) = k1_xboole_0
% 3.33/1.02      | u1_struct_0(sK4) != X0
% 3.33/1.02      | sK6 != sK6
% 3.33/1.02      | k1_xboole_0 = X1 ),
% 3.33/1.02      inference(resolution_lifted,[status(thm)],[c_1140,c_1194]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1407,plain,
% 3.33/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0)))
% 3.33/1.02      | k8_relset_1(u1_struct_0(sK4),X0,sK6,X0) = u1_struct_0(sK4)
% 3.33/1.02      | u1_struct_0(sK5) = k1_xboole_0
% 3.33/1.02      | k1_xboole_0 = X0 ),
% 3.33/1.02      inference(unflattening,[status(thm)],[c_1406]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3040,plain,
% 3.33/1.02      ( k8_relset_1(u1_struct_0(sK4),X0,sK6,X0) = u1_struct_0(sK4)
% 3.33/1.02      | u1_struct_0(sK5) = k1_xboole_0
% 3.33/1.02      | k1_xboole_0 = X0
% 3.33/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_1407]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4017,plain,
% 3.33/1.02      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,u1_struct_0(sK5)) = u1_struct_0(sK4)
% 3.33/1.02      | u1_struct_0(sK5) = k1_xboole_0 ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3066,c_3040]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3439,plain,
% 3.33/1.02      ( ~ l1_orders_2(sK5)
% 3.33/1.02      | v2_struct_0(sK5)
% 3.33/1.02      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 3.33/1.02      inference(instantiation,[status(thm)],[c_613]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4347,plain,
% 3.33/1.02      ( ~ v1_xboole_0(X0)
% 3.33/1.02      | v1_xboole_0(u1_struct_0(sK5))
% 3.33/1.02      | u1_struct_0(sK5) != X0 ),
% 3.33/1.02      inference(instantiation,[status(thm)],[c_2031]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4349,plain,
% 3.33/1.02      ( v1_xboole_0(u1_struct_0(sK5))
% 3.33/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 3.33/1.02      | u1_struct_0(sK5) != k1_xboole_0 ),
% 3.33/1.02      inference(instantiation,[status(thm)],[c_4347]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4377,plain,
% 3.33/1.02      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,u1_struct_0(sK5)) = u1_struct_0(sK4) ),
% 3.33/1.02      inference(global_propositional_subsumption,
% 3.33/1.02                [status(thm)],
% 3.33/1.02                [c_4017,c_44,c_43,c_135,c_591,c_3439,c_3525,c_4349]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6170,plain,
% 3.33/1.02      ( k8_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,u1_struct_0(sK5)) = k1_relat_1(sK6) ),
% 3.33/1.02      inference(demodulation,[status(thm)],[c_6158,c_4377]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6902,plain,
% 3.33/1.02      ( k7_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
% 3.33/1.02      inference(light_normalisation,[status(thm)],[c_6452,c_6166,c_6170]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6907,plain,
% 3.33/1.02      ( k8_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,k2_relat_1(sK6)) = k1_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6) ),
% 3.33/1.02      inference(light_normalisation,[status(thm)],[c_6565,c_6902]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_34,plain,
% 3.33/1.02      ( ~ m1_yellow_0(X0,X1)
% 3.33/1.02      | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 3.33/1.02      | ~ l1_orders_2(X1)
% 3.33/1.02      | ~ l1_orders_2(X0) ),
% 3.33/1.02      inference(cnf_transformation,[],[f117]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_267,plain,
% 3.33/1.02      ( ~ l1_orders_2(X1)
% 3.33/1.02      | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 3.33/1.02      | ~ m1_yellow_0(X0,X1) ),
% 3.33/1.02      inference(global_propositional_subsumption,[status(thm)],[c_34,c_36]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_268,plain,
% 3.33/1.02      ( ~ m1_yellow_0(X0,X1)
% 3.33/1.02      | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 3.33/1.02      | ~ l1_orders_2(X1) ),
% 3.33/1.02      inference(renaming,[status(thm)],[c_267]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1082,plain,
% 3.33/1.02      ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 3.33/1.02      | ~ l1_orders_2(X1)
% 3.33/1.02      | ~ l1_orders_2(X2)
% 3.33/1.02      | v2_struct_0(X2)
% 3.33/1.02      | X2 != X1
% 3.33/1.02      | sK3(X2) != X0 ),
% 3.33/1.02      inference(resolution_lifted,[status(thm)],[c_268,c_38]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1083,plain,
% 3.33/1.02      ( r1_tarski(u1_orders_2(sK3(X0)),u1_orders_2(X0))
% 3.33/1.02      | ~ l1_orders_2(X0)
% 3.33/1.02      | v2_struct_0(X0) ),
% 3.33/1.02      inference(unflattening,[status(thm)],[c_1082]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3059,plain,
% 3.33/1.02      ( r1_tarski(u1_orders_2(sK3(X0)),u1_orders_2(X0)) = iProver_top
% 3.33/1.02      | l1_orders_2(X0) != iProver_top
% 3.33/1.02      | v2_struct_0(X0) = iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_1083]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6444,plain,
% 3.33/1.02      ( u1_orders_2(sK3(X0)) = u1_orders_2(X0)
% 3.33/1.02      | r1_tarski(u1_orders_2(X0),u1_orders_2(sK3(X0))) != iProver_top
% 3.33/1.02      | l1_orders_2(X0) != iProver_top
% 3.33/1.02      | v2_struct_0(X0) = iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3059,c_3085]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3042,plain,
% 3.33/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top
% 3.33/1.02      | sP1_iProver_split != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_2017]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6385,plain,
% 3.33/1.02      ( sP1_iProver_split != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_6178,c_3042]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1157,plain,
% 3.33/1.02      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.33/1.02      | k2_funct_1(sK6) != sK6
% 3.33/1.02      | u1_struct_0(sK5) != u1_struct_0(sK4)
% 3.33/1.02      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 3.33/1.02      inference(resolution_lifted,[status(thm)],[c_812,c_41]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3056,plain,
% 3.33/1.02      ( k2_funct_1(sK6) != sK6
% 3.33/1.02      | u1_struct_0(sK5) != u1_struct_0(sK4)
% 3.33/1.02      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
% 3.33/1.02      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_1157]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6176,plain,
% 3.33/1.02      ( k2_funct_1(sK6) != sK6
% 3.33/1.02      | u1_struct_0(sK5) != k1_relat_1(sK6)
% 3.33/1.02      | k2_relat_1(k2_funct_1(sK6)) != k1_relat_1(sK6)
% 3.33/1.02      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_relat_1(sK6)))) != iProver_top ),
% 3.33/1.02      inference(demodulation,[status(thm)],[c_6158,c_3056]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_24,plain,
% 3.33/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.33/1.02      | v1_partfun1(X0,k1_xboole_0)
% 3.33/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.33/1.02      | ~ v1_funct_1(X0) ),
% 3.33/1.02      inference(cnf_transformation,[],[f135]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_782,plain,
% 3.33/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.33/1.02      | v1_partfun1(X0,k1_xboole_0)
% 3.33/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.33/1.02      | sK6 != X0 ),
% 3.33/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_42]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_783,plain,
% 3.33/1.02      ( ~ v1_funct_2(sK6,k1_xboole_0,X0)
% 3.33/1.02      | v1_partfun1(sK6,k1_xboole_0)
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
% 3.33/1.02      inference(unflattening,[status(thm)],[c_782]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1216,plain,
% 3.33/1.02      ( v1_partfun1(sK6,k1_xboole_0)
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 3.33/1.02      | u1_struct_0(sK5) != X0
% 3.33/1.02      | u1_struct_0(sK4) != k1_xboole_0
% 3.33/1.02      | sK6 != sK6 ),
% 3.33/1.02      inference(resolution_lifted,[status(thm)],[c_41,c_783]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1217,plain,
% 3.33/1.02      ( v1_partfun1(sK6,k1_xboole_0)
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
% 3.33/1.02      | u1_struct_0(sK4) != k1_xboole_0 ),
% 3.33/1.02      inference(unflattening,[status(thm)],[c_1216]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1311,plain,
% 3.33/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
% 3.33/1.02      | u1_struct_0(sK4) != k1_xboole_0
% 3.33/1.02      | k1_relat_1(X0) = X1
% 3.33/1.02      | sK6 != X0
% 3.33/1.02      | k1_xboole_0 != X1 ),
% 3.33/1.02      inference(resolution_lifted,[status(thm)],[c_659,c_1217]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1312,plain,
% 3.33/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
% 3.33/1.02      | u1_struct_0(sK4) != k1_xboole_0
% 3.33/1.02      | k1_relat_1(sK6) = k1_xboole_0 ),
% 3.33/1.02      inference(unflattening,[status(thm)],[c_1311]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_2025,plain,
% 3.33/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
% 3.33/1.02      | sP4_iProver_split
% 3.33/1.02      | u1_struct_0(sK4) != k1_xboole_0
% 3.33/1.02      | k1_relat_1(sK6) = k1_xboole_0 ),
% 3.33/1.02      inference(splitting,
% 3.33/1.02                [splitting(split),new_symbols(definition,[])],
% 3.33/1.02                [c_1312]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3051,plain,
% 3.33/1.02      ( u1_struct_0(sK4) != k1_xboole_0
% 3.33/1.02      | k1_relat_1(sK6) = k1_xboole_0
% 3.33/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5)))) != iProver_top
% 3.33/1.02      | sP4_iProver_split = iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_2025]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_2024,plain,
% 3.33/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 3.33/1.02      | ~ sP4_iProver_split ),
% 3.33/1.02      inference(splitting,
% 3.33/1.02                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 3.33/1.02                [c_1312]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3052,plain,
% 3.33/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 3.33/1.02      | sP4_iProver_split != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_2024]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3260,plain,
% 3.33/1.02      ( u1_struct_0(sK4) != k1_xboole_0
% 3.33/1.02      | k1_relat_1(sK6) = k1_xboole_0
% 3.33/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5)))) != iProver_top ),
% 3.33/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_3051,c_3052]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3442,plain,
% 3.33/1.02      ( ~ l1_orders_2(sK4)
% 3.33/1.02      | v2_struct_0(sK4)
% 3.33/1.02      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 3.33/1.02      inference(instantiation,[status(thm)],[c_613]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4352,plain,
% 3.33/1.02      ( ~ v1_xboole_0(X0)
% 3.33/1.02      | v1_xboole_0(u1_struct_0(sK4))
% 3.33/1.02      | u1_struct_0(sK4) != X0 ),
% 3.33/1.02      inference(instantiation,[status(thm)],[c_2031]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4354,plain,
% 3.33/1.02      ( v1_xboole_0(u1_struct_0(sK4))
% 3.33/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 3.33/1.02      | u1_struct_0(sK4) != k1_xboole_0 ),
% 3.33/1.02      inference(instantiation,[status(thm)],[c_4352]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4443,plain,
% 3.33/1.02      ( u1_struct_0(sK4) != k1_xboole_0 ),
% 3.33/1.02      inference(global_propositional_subsumption,
% 3.33/1.02                [status(thm)],
% 3.33/1.02                [c_3260,c_46,c_45,c_135,c_591,c_3442,c_3525,c_4354]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6168,plain,
% 3.33/1.02      ( k1_relat_1(sK6) != k1_xboole_0 ),
% 3.33/1.02      inference(demodulation,[status(thm)],[c_6158,c_4443]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6164,plain,
% 3.33/1.02      ( k7_relat_1(sK6,k1_relat_1(sK6)) = sK6 ),
% 3.33/1.02      inference(demodulation,[status(thm)],[c_6158,c_5678]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_5799,plain,
% 3.33/1.02      ( k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6,X0) = k9_relat_1(sK6,X0) ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3066,c_3073]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_6163,plain,
% 3.33/1.02      ( k7_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6,X0) = k9_relat_1(sK6,X0) ),
% 3.33/1.02      inference(demodulation,[status(thm)],[c_6158,c_5799]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_5861,plain,
% 3.33/1.02      ( sK0(X0,X1) = X0
% 3.33/1.02      | k1_zfmisc_1(X0) = X1
% 3.33/1.02      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.33/1.02      | r1_tarski(X0,sK0(X0,X1)) != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3081,c_3085]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_5777,plain,
% 3.33/1.02      ( u1_struct_0(sK3(X0)) = u1_struct_0(X0)
% 3.33/1.02      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3(X0))) != iProver_top
% 3.33/1.02      | l1_orders_2(X0) != iProver_top
% 3.33/1.02      | v2_struct_0(X0) = iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3058,c_3085]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_30,plain,
% 3.33/1.02      ( r2_hidden(sK2(X0),X0) | k3_tarski(X0) = k1_xboole_0 ),
% 3.33/1.02      inference(cnf_transformation,[],[f115]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3069,plain,
% 3.33/1.02      ( k3_tarski(X0) = k1_xboole_0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4261,plain,
% 3.33/1.02      ( k3_tarski(k1_zfmisc_1(X0)) = k1_xboole_0
% 3.33/1.02      | r1_tarski(sK2(k1_zfmisc_1(X0)),X0) = iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_3069,c_3079]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4262,plain,
% 3.33/1.02      ( k1_xboole_0 = X0 | r1_tarski(sK2(k1_zfmisc_1(X0)),X0) = iProver_top ),
% 3.33/1.02      inference(demodulation,[status(thm)],[c_4261,c_8]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_5776,plain,
% 3.33/1.02      ( sK2(k1_zfmisc_1(X0)) = X0
% 3.33/1.02      | k1_xboole_0 = X0
% 3.33/1.02      | r1_tarski(X0,sK2(k1_zfmisc_1(X0))) != iProver_top ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_4262,c_3085]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_5303,plain,
% 3.33/1.02      ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 3.33/1.02      inference(superposition,[status(thm)],[c_4863,c_3074]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_4864,plain,
% 3.33/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.33/1.02      inference(demodulation,[status(thm)],[c_4188,c_3078]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3046,plain,
% 3.33/1.02      ( sP2_iProver_split = iProver_top | sP1_iProver_split = iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_2021]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_26,plain,
% 3.33/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.33/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.33/1.02      | ~ v1_funct_1(X0)
% 3.33/1.02      | k8_relset_1(k1_xboole_0,X1,X0,X1) = k1_xboole_0 ),
% 3.33/1.02      inference(cnf_transformation,[],[f136]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_749,plain,
% 3.33/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.33/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.33/1.02      | k8_relset_1(k1_xboole_0,X1,X0,X1) = k1_xboole_0
% 3.33/1.02      | sK6 != X0 ),
% 3.33/1.02      inference(resolution_lifted,[status(thm)],[c_26,c_42]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_750,plain,
% 3.33/1.02      ( ~ v1_funct_2(sK6,k1_xboole_0,X0)
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 3.33/1.02      | k8_relset_1(k1_xboole_0,X0,sK6,X0) = k1_xboole_0 ),
% 3.33/1.02      inference(unflattening,[status(thm)],[c_749]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1244,plain,
% 3.33/1.02      ( ~ v1_partfun1(sK6,X0)
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 3.33/1.02      | X2 != X1
% 3.33/1.02      | k8_relset_1(k1_xboole_0,X2,sK6,X2) = k1_xboole_0
% 3.33/1.02      | sK6 != sK6
% 3.33/1.02      | k1_xboole_0 != X0 ),
% 3.33/1.02      inference(resolution_lifted,[status(thm)],[c_798,c_750]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1245,plain,
% 3.33/1.02      ( ~ v1_partfun1(sK6,k1_xboole_0)
% 3.33/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 3.33/1.02      | k8_relset_1(k1_xboole_0,X0,sK6,X0) = k1_xboole_0 ),
% 3.33/1.02      inference(unflattening,[status(thm)],[c_1244]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1451,plain,
% 3.33/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 3.33/1.02      | k8_relset_1(k1_xboole_0,X0,sK6,X0) = k1_xboole_0
% 3.33/1.02      | u1_struct_0(sK5) = k1_xboole_0
% 3.33/1.02      | u1_struct_0(sK4) != k1_xboole_0
% 3.33/1.02      | sK6 != sK6 ),
% 3.33/1.02      inference(resolution_lifted,[status(thm)],[c_1245,c_1194]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_1568,plain,
% 3.33/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 3.33/1.02      | k8_relset_1(k1_xboole_0,X0,sK6,X0) = k1_xboole_0
% 3.33/1.02      | u1_struct_0(sK5) = k1_xboole_0
% 3.33/1.02      | u1_struct_0(sK4) != k1_xboole_0 ),
% 3.33/1.02      inference(equality_resolution_simp,[status(thm)],[c_1451]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_2015,plain,
% 3.33/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 3.33/1.02      | k8_relset_1(k1_xboole_0,X0,sK6,X0) = k1_xboole_0
% 3.33/1.02      | ~ sP0_iProver_split ),
% 3.33/1.02      inference(splitting,
% 3.33/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.33/1.02                [c_1568]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3039,plain,
% 3.33/1.02      ( k8_relset_1(k1_xboole_0,X0,sK6,X0) = k1_xboole_0
% 3.33/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 3.33/1.02      | sP0_iProver_split != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_2015]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3057,plain,
% 3.33/1.02      ( l1_orders_2(X0) != iProver_top
% 3.33/1.02      | l1_orders_2(sK3(X0)) = iProver_top
% 3.33/1.02      | v2_struct_0(X0) = iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_1113]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3067,plain,
% 3.33/1.02      ( l1_orders_2(X0) != iProver_top
% 3.33/1.02      | v2_struct_0(X0) = iProver_top
% 3.33/1.02      | v2_struct_0(sK3(X0)) != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3065,plain,
% 3.33/1.02      ( l1_orders_2(sK5) = iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3064,plain,
% 3.33/1.02      ( v2_struct_0(sK5) != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3063,plain,
% 3.33/1.02      ( l1_orders_2(sK4) = iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_3062,plain,
% 3.33/1.02      ( v2_struct_0(sK4) != iProver_top ),
% 3.33/1.02      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.33/1.02  
% 3.33/1.02  cnf(c_31,plain,
% 3.33/1.02      ( sK2(X0) != k1_xboole_0 | k3_tarski(X0) = k1_xboole_0 ),
% 3.33/1.02      inference(cnf_transformation,[],[f114]) ).
% 3.33/1.02  
% 3.33/1.02  
% 3.33/1.02  % SZS output end Saturation for theBenchmark.p
% 3.33/1.02  
% 3.33/1.02  ------                               Statistics
% 3.33/1.02  
% 3.33/1.02  ------ General
% 3.33/1.02  
% 3.33/1.02  abstr_ref_over_cycles:                  0
% 3.33/1.02  abstr_ref_under_cycles:                 0
% 3.33/1.02  gc_basic_clause_elim:                   0
% 3.33/1.02  forced_gc_time:                         0
% 3.33/1.02  parsing_time:                           0.01
% 3.33/1.02  unif_index_cands_time:                  0.
% 3.33/1.02  unif_index_add_time:                    0.
% 3.33/1.02  orderings_time:                         0.
% 3.33/1.02  out_proof_time:                         0.
% 3.33/1.02  total_time:                             0.292
% 3.33/1.02  num_of_symbols:                         71
% 3.33/1.02  num_of_terms:                           7923
% 3.33/1.02  
% 3.33/1.02  ------ Preprocessing
% 3.33/1.02  
% 3.33/1.02  num_of_splits:                          9
% 3.33/1.02  num_of_split_atoms:                     5
% 3.33/1.02  num_of_reused_defs:                     4
% 3.33/1.02  num_eq_ax_congr_red:                    65
% 3.33/1.02  num_of_sem_filtered_clauses:            2
% 3.33/1.02  num_of_subtypes:                        0
% 3.33/1.02  monotx_restored_types:                  0
% 3.33/1.02  sat_num_of_epr_types:                   0
% 3.33/1.02  sat_num_of_non_cyclic_types:            0
% 3.33/1.02  sat_guarded_non_collapsed_types:        0
% 3.33/1.02  num_pure_diseq_elim:                    0
% 3.33/1.02  simp_replaced_by:                       0
% 3.33/1.02  res_preprocessed:                       220
% 3.33/1.02  prep_upred:                             0
% 3.33/1.02  prep_unflattend:                        75
% 3.33/1.02  smt_new_axioms:                         0
% 3.33/1.02  pred_elim_cands:                        7
% 3.33/1.02  pred_elim:                              6
% 3.33/1.02  pred_elim_cl:                           2
% 3.33/1.02  pred_elim_cycles:                       15
% 3.33/1.02  merged_defs:                            8
% 3.33/1.02  merged_defs_ncl:                        0
% 3.33/1.02  bin_hyper_res:                          8
% 3.33/1.02  prep_cycles:                            4
% 3.33/1.02  pred_elim_time:                         0.029
% 3.33/1.02  splitting_time:                         0.
% 3.33/1.02  sem_filter_time:                        0.
% 3.33/1.02  monotx_time:                            0.
% 3.33/1.02  subtype_inf_time:                       0.
% 3.33/1.02  
% 3.33/1.02  ------ Problem properties
% 3.33/1.02  
% 3.33/1.02  clauses:                                52
% 3.33/1.02  conjectures:                            5
% 3.33/1.02  epr:                                    8
% 3.33/1.02  horn:                                   39
% 3.33/1.02  ground:                                 16
% 3.33/1.02  unary:                                  9
% 3.33/1.02  binary:                                 19
% 3.33/1.02  lits:                                   130
% 3.33/1.02  lits_eq:                                46
% 3.33/1.02  fd_pure:                                0
% 3.33/1.02  fd_pseudo:                              0
% 3.33/1.02  fd_cond:                                4
% 3.33/1.02  fd_pseudo_cond:                         3
% 3.33/1.02  ac_symbols:                             0
% 3.33/1.02  
% 3.33/1.02  ------ Propositional Solver
% 3.33/1.02  
% 3.33/1.02  prop_solver_calls:                      29
% 3.33/1.02  prop_fast_solver_calls:                 1628
% 3.33/1.02  smt_solver_calls:                       0
% 3.33/1.02  smt_fast_solver_calls:                  0
% 3.33/1.02  prop_num_of_clauses:                    3562
% 3.33/1.02  prop_preprocess_simplified:             11374
% 3.33/1.02  prop_fo_subsumed:                       22
% 3.33/1.02  prop_solver_time:                       0.
% 3.33/1.02  smt_solver_time:                        0.
% 3.33/1.02  smt_fast_solver_time:                   0.
% 3.33/1.02  prop_fast_solver_time:                  0.
% 3.33/1.02  prop_unsat_core_time:                   0.
% 3.33/1.02  
% 3.33/1.02  ------ QBF
% 3.33/1.02  
% 3.33/1.02  qbf_q_res:                              0
% 3.33/1.02  qbf_num_tautologies:                    0
% 3.33/1.02  qbf_prep_cycles:                        0
% 3.33/1.02  
% 3.33/1.02  ------ BMC1
% 3.33/1.02  
% 3.33/1.02  bmc1_current_bound:                     -1
% 3.33/1.02  bmc1_last_solved_bound:                 -1
% 3.33/1.02  bmc1_unsat_core_size:                   -1
% 3.33/1.02  bmc1_unsat_core_parents_size:           -1
% 3.33/1.02  bmc1_merge_next_fun:                    0
% 3.33/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.33/1.02  
% 3.33/1.02  ------ Instantiation
% 3.33/1.02  
% 3.33/1.02  inst_num_of_clauses:                    1156
% 3.33/1.02  inst_num_in_passive:                    552
% 3.33/1.02  inst_num_in_active:                     563
% 3.33/1.02  inst_num_in_unprocessed:                41
% 3.33/1.02  inst_num_of_loops:                      610
% 3.33/1.02  inst_num_of_learning_restarts:          0
% 3.33/1.02  inst_num_moves_active_passive:          44
% 3.33/1.02  inst_lit_activity:                      0
% 3.33/1.02  inst_lit_activity_moves:                0
% 3.33/1.02  inst_num_tautologies:                   0
% 3.33/1.02  inst_num_prop_implied:                  0
% 3.33/1.02  inst_num_existing_simplified:           0
% 3.33/1.02  inst_num_eq_res_simplified:             0
% 3.33/1.02  inst_num_child_elim:                    0
% 3.33/1.02  inst_num_of_dismatching_blockings:      303
% 3.33/1.02  inst_num_of_non_proper_insts:           981
% 3.33/1.02  inst_num_of_duplicates:                 0
% 3.33/1.02  inst_inst_num_from_inst_to_res:         0
% 3.33/1.02  inst_dismatching_checking_time:         0.
% 3.33/1.02  
% 3.33/1.02  ------ Resolution
% 3.33/1.02  
% 3.33/1.02  res_num_of_clauses:                     0
% 3.33/1.02  res_num_in_passive:                     0
% 3.33/1.02  res_num_in_active:                      0
% 3.33/1.02  res_num_of_loops:                       224
% 3.33/1.02  res_forward_subset_subsumed:            52
% 3.33/1.02  res_backward_subset_subsumed:           2
% 3.33/1.02  res_forward_subsumed:                   1
% 3.33/1.02  res_backward_subsumed:                  0
% 3.33/1.02  res_forward_subsumption_resolution:     1
% 3.33/1.02  res_backward_subsumption_resolution:    0
% 3.33/1.02  res_clause_to_clause_subsumption:       308
% 3.33/1.02  res_orphan_elimination:                 0
% 3.33/1.02  res_tautology_del:                      117
% 3.33/1.02  res_num_eq_res_simplified:              2
% 3.33/1.02  res_num_sel_changes:                    0
% 3.33/1.02  res_moves_from_active_to_pass:          0
% 3.33/1.02  
% 3.33/1.02  ------ Superposition
% 3.33/1.02  
% 3.33/1.02  sup_time_total:                         0.
% 3.33/1.02  sup_time_generating:                    0.
% 3.33/1.02  sup_time_sim_full:                      0.
% 3.33/1.02  sup_time_sim_immed:                     0.
% 3.33/1.02  
% 3.33/1.02  sup_num_of_clauses:                     96
% 3.33/1.02  sup_num_in_active:                      92
% 3.33/1.02  sup_num_in_passive:                     4
% 3.33/1.02  sup_num_of_loops:                       120
% 3.33/1.02  sup_fw_superposition:                   69
% 3.33/1.02  sup_bw_superposition:                   52
% 3.33/1.02  sup_immediate_simplified:               32
% 3.33/1.02  sup_given_eliminated:                   0
% 3.33/1.02  comparisons_done:                       0
% 3.33/1.02  comparisons_avoided:                    21
% 3.33/1.02  
% 3.33/1.02  ------ Simplifications
% 3.33/1.02  
% 3.33/1.02  
% 3.33/1.02  sim_fw_subset_subsumed:                 17
% 3.33/1.02  sim_bw_subset_subsumed:                 7
% 3.33/1.02  sim_fw_subsumed:                        5
% 3.33/1.02  sim_bw_subsumed:                        4
% 3.33/1.02  sim_fw_subsumption_res:                 1
% 3.33/1.02  sim_bw_subsumption_res:                 0
% 3.33/1.02  sim_tautology_del:                      4
% 3.33/1.02  sim_eq_tautology_del:                   19
% 3.33/1.02  sim_eq_res_simp:                        0
% 3.33/1.02  sim_fw_demodulated:                     7
% 3.33/1.02  sim_bw_demodulated:                     23
% 3.33/1.02  sim_light_normalised:                   7
% 3.33/1.02  sim_joinable_taut:                      0
% 3.33/1.02  sim_joinable_simp:                      0
% 3.33/1.02  sim_ac_normalised:                      0
% 3.33/1.02  sim_smt_subsumption:                    0
% 3.33/1.02  
%------------------------------------------------------------------------------
