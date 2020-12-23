%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:12 EST 2020

% Result     : CounterSatisfiable 2.59s
% Output     : Saturation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  290 (3720 expanded)
%              Number of clauses        :  182 (1110 expanded)
%              Number of leaves         :   33 ( 902 expanded)
%              Depth                    :   28
%              Number of atoms          :  995 (24003 expanded)
%              Number of equality atoms :  361 (3743 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
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

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f56,plain,(
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

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f55,f56])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | r1_tarski(sK0(X0,X1),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f114,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f113,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f4,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f17,axiom,(
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

fof(f23,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK2(X0),X0)
        & k1_xboole_0 != sK2(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK2(X0),X0)
          & k1_xboole_0 != sK2(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f61])).

fof(f94,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | ~ r1_tarski(sK0(X0,X1),X0)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f24,plain,(
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
    inference(pure_predicate_removal,[],[f22])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f69,plain,(
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

fof(f68,plain,(
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

fof(f67,plain,
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

fof(f70,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f51,f69,f68,f67])).

fof(f108,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f70])).

fof(f13,axiom,(
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

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f107,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f109,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f70])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f100,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_yellow_0(X1,X0)
          & v1_orders_2(X1)
          & ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_orders_2(X1)
          & ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f26,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) )
     => ( ~ v2_struct_0(sK3(X0))
        & m1_yellow_0(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ( ~ v2_struct_0(sK3(X0))
        & m1_yellow_0(sK3(X0),X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f65])).

fof(f101,plain,(
    ! [X0] :
      ( m1_yellow_0(sK3(X0),X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f105,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f70])).

fof(f106,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f70])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1(X0))
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f58])).

fof(f81,plain,(
    ! [X0] : v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK3(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f93,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f103,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f70])).

fof(f104,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f70])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f116,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f91])).

fof(f110,plain,
    ( k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f70])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f112,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f34])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f115,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f96,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK2(X0)
      | k1_xboole_0 = k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_461,plain,
    ( ~ m1_yellow_0(X0,X1)
    | m1_yellow_0(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_457,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_456,plain,
    ( ~ v1_partfun1(X0,X1)
    | v1_partfun1(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_455,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_453,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_1481,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(sK0(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2253,plain,
    ( k1_zfmisc_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_tarski(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2251,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4044,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) = iProver_top
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2253,c_2251])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2256,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5346,plain,
    ( sK0(X0,k1_zfmisc_1(X1)) = X0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(X0,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4044,c_2256])).

cnf(c_5341,plain,
    ( sK0(X0,k1_zfmisc_1(X1)) = X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(X1,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4044,c_2256])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2252,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2245,plain,
    ( k3_tarski(X0) != k1_xboole_0
    | k1_xboole_0 = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3665,plain,
    ( k1_xboole_0 != X0
    | k1_xboole_0 = X1
    | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_2245])).

cnf(c_3736,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3665])).

cnf(c_3741,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2252,c_3736])).

cnf(c_4256,plain,
    ( sK0(k1_xboole_0,X0) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2253,c_3741])).

cnf(c_5159,plain,
    ( sK0(k1_xboole_0,k1_zfmisc_1(X0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(sK0(k1_xboole_0,k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4256,c_2251])).

cnf(c_5278,plain,
    ( sK0(k1_xboole_0,k1_zfmisc_1(X0)) = X0
    | sK0(k1_xboole_0,k1_zfmisc_1(X0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(X0,sK0(k1_xboole_0,k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5159,c_2256])).

cnf(c_4045,plain,
    ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(sK0(X0,k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2253,c_3736])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r1_tarski(sK0(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2254,plain,
    ( k1_zfmisc_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(sK0(X0,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4593,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) != iProver_top
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2252,c_2254])).

cnf(c_5231,plain,
    ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(sK0(X0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4045,c_4593])).

cnf(c_5214,plain,
    ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = X0
    | sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(X0,sK0(X0,k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4045,c_2256])).

cnf(c_5158,plain,
    ( sK0(k1_xboole_0,X0) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = X0
    | r1_tarski(sK0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4256,c_2254])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_18,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_602,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_12,c_18])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_602,c_18,c_12,c_11])).

cnf(c_607,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_606])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_646,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_647,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_762,plain,
    ( v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | u1_struct_0(sK5) != X1
    | u1_struct_0(sK4) != X0
    | sK6 != sK6
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_647])).

cnf(c_763,plain,
    ( v1_partfun1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | k1_xboole_0 = u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_765,plain,
    ( v1_partfun1(sK6,u1_struct_0(sK4))
    | k1_xboole_0 = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_763,c_33])).

cnf(c_829,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | u1_struct_0(sK5) = k1_xboole_0
    | u1_struct_0(sK4) != X1
    | k1_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_607,c_765])).

cnf(c_830,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0)))
    | u1_struct_0(sK5) = k1_xboole_0
    | k1_relat_1(sK6) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_1478,plain,
    ( sP1_iProver_split
    | u1_struct_0(sK5) = k1_xboole_0
    | k1_relat_1(sK6) = u1_struct_0(sK4) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_830])).

cnf(c_2233,plain,
    ( u1_struct_0(sK5) = k1_xboole_0
    | k1_relat_1(sK6) = u1_struct_0(sK4)
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1478])).

cnf(c_2243,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1477,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_830])).

cnf(c_2234,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1477])).

cnf(c_2558,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2243,c_2234])).

cnf(c_2559,plain,
    ( ~ sP1_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2558])).

cnf(c_2895,plain,
    ( k1_relat_1(sK6) = u1_struct_0(sK4)
    | u1_struct_0(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2233,c_1478,c_2559])).

cnf(c_2896,plain,
    ( u1_struct_0(sK5) = k1_xboole_0
    | k1_relat_1(sK6) = u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_2895])).

cnf(c_28,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_29,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_220,plain,
    ( ~ l1_orders_2(X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_yellow_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_29])).

cnf(c_221,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_220])).

cnf(c_31,plain,
    ( m1_yellow_0(sK3(X0),X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1058,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | X2 != X1
    | sK3(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_221,c_31])).

cnf(c_1059,plain,
    ( r1_tarski(u1_struct_0(sK3(X0)),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1058])).

cnf(c_2229,plain,
    ( r1_tarski(u1_struct_0(sK3(X0)),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1059])).

cnf(c_3867,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK6)
    | r1_tarski(u1_struct_0(sK3(sK5)),k1_xboole_0) = iProver_top
    | l1_orders_2(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2896,c_2229])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_42,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_43,plain,
    ( l1_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4111,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK6)
    | r1_tarski(u1_struct_0(sK3(sK5)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3867,c_42,c_43])).

cnf(c_4258,plain,
    ( u1_struct_0(sK3(sK5)) = k1_xboole_0
    | u1_struct_0(sK4) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_4111,c_3741])).

cnf(c_9,plain,
    ( v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_107,plain,
    ( v1_xboole_0(sK1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_499,plain,
    ( sK1(X0) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_500,plain,
    ( k1_xboole_0 = sK1(X0) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_501,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_30,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2492,plain,
    ( ~ l1_orders_2(sK5)
    | ~ v2_struct_0(sK3(sK5))
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1073,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X2)
    | v2_struct_0(X1)
    | X1 != X0
    | sK3(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_31])).

cnf(c_1074,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(sK3(X0))
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1073])).

cnf(c_2508,plain,
    ( l1_orders_2(sK3(sK5))
    | ~ l1_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_1484,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2608,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK1(X1))
    | X0 != sK1(X1) ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_2610,plain,
    ( ~ v1_xboole_0(sK1(k1_xboole_0))
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2608])).

cnf(c_22,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_21,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_523,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_22,c_21])).

cnf(c_2629,plain,
    ( ~ l1_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ v1_xboole_0(u1_struct_0(sK3(sK5))) ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_3356,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK3(sK5)))
    | u1_struct_0(sK3(sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_3358,plain,
    ( v1_xboole_0(u1_struct_0(sK3(sK5)))
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(sK3(sK5)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3356])).

cnf(c_4272,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4258,c_37,c_36,c_107,c_501,c_2492,c_2508,c_2610,c_2629,c_3358])).

cnf(c_4312,plain,
    ( r1_tarski(u1_struct_0(sK3(sK4)),k1_relat_1(sK6)) = iProver_top
    | l1_orders_2(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4272,c_2229])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_40,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_41,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5072,plain,
    ( r1_tarski(u1_struct_0(sK3(sK4)),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4312,c_40,c_41])).

cnf(c_5077,plain,
    ( u1_struct_0(sK3(sK4)) = k1_relat_1(sK6)
    | r1_tarski(k1_relat_1(sK6),u1_struct_0(sK3(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5072,c_2256])).

cnf(c_2238,plain,
    ( l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_4699,plain,
    ( l1_orders_2(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4272,c_2238])).

cnf(c_5066,plain,
    ( v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4699,c_40,c_41])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_664,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_665,plain,
    ( ~ v1_funct_2(sK6,k1_xboole_0,X0)
    | v1_partfun1(sK6,k1_xboole_0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_776,plain,
    ( v1_partfun1(sK6,k1_xboole_0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | u1_struct_0(sK5) != X0
    | u1_struct_0(sK4) != k1_xboole_0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_665])).

cnf(c_777,plain,
    ( v1_partfun1(sK6,k1_xboole_0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
    | u1_struct_0(sK4) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_776])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_694,plain,
    ( ~ v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | k2_funct_1(sK6) != sK6
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_32,c_35])).

cnf(c_15,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_679,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_35])).

cnf(c_680,plain,
    ( v1_funct_2(sK6,X0,X1)
    | ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_743,plain,
    ( ~ v1_partfun1(sK6,X0)
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_funct_1(sK6) != sK6
    | u1_struct_0(sK5) != X0
    | u1_struct_0(sK4) != X1
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_694,c_680])).

cnf(c_744,plain,
    ( ~ v1_partfun1(sK6,u1_struct_0(sK5))
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | k2_funct_1(sK6) != sK6
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_868,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
    | k2_funct_1(sK6) != sK6
    | u1_struct_0(sK5) != k1_xboole_0
    | u1_struct_0(sK4) != k1_xboole_0
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_777,c_744])).

cnf(c_1131,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
    | k2_funct_1(sK6) != sK6
    | u1_struct_0(sK5) != k1_xboole_0
    | u1_struct_0(sK4) != k1_xboole_0
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_868])).

cnf(c_2227,plain,
    ( k2_funct_1(sK6) != sK6
    | u1_struct_0(sK5) != k1_xboole_0
    | u1_struct_0(sK4) != k1_xboole_0
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1131])).

cnf(c_4279,plain,
    ( k2_funct_1(sK6) != sK6
    | u1_struct_0(sK5) != k1_xboole_0
    | k1_relat_1(sK6) != k1_xboole_0
    | k2_relat_1(k2_funct_1(sK6)) != k1_relat_1(sK6)
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_relat_1(sK6)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_relat_1(sK6)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4272,c_2227])).

cnf(c_2502,plain,
    ( ~ l1_orders_2(sK5)
    | v2_struct_0(sK5)
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_3346,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK5))
    | u1_struct_0(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_3348,plain,
    ( v1_xboole_0(u1_struct_0(sK5))
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3346])).

cnf(c_5008,plain,
    ( u1_struct_0(sK5) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4279,c_37,c_36,c_107,c_501,c_2502,c_2610,c_3348])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2255,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4282,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK5)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4272,c_2243])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2247,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4606,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4282,c_2247])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2248,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4712,plain,
    ( k2_relset_1(k1_relat_1(sK6),X0,sK6) = k2_relat_1(sK6)
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4606,c_2248])).

cnf(c_4903,plain,
    ( k2_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2255,c_4712])).

cnf(c_27,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_225,plain,
    ( ~ l1_orders_2(X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ m1_yellow_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_29])).

cnf(c_226,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_225])).

cnf(c_1043,plain,
    ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | X2 != X1
    | sK3(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_226,c_31])).

cnf(c_1044,plain,
    ( r1_tarski(u1_orders_2(sK3(X0)),u1_orders_2(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1043])).

cnf(c_2230,plain,
    ( r1_tarski(u1_orders_2(sK3(X0)),u1_orders_2(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1044])).

cnf(c_4455,plain,
    ( u1_orders_2(sK3(X0)) = u1_orders_2(X0)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(sK3(X0))) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2230,c_2256])).

cnf(c_17,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v4_relat_1(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_622,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k1_relat_1(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_623,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_633,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_623,c_11])).

cnf(c_844,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | k2_funct_1(sK6) != sK6
    | k1_relat_1(X0) != u1_struct_0(sK5)
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_633,c_744])).

cnf(c_845,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)))
    | k2_funct_1(sK6) != sK6
    | k1_relat_1(sK6) != u1_struct_0(sK5)
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_1475,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_845])).

cnf(c_2232,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1475])).

cnf(c_4447,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4282,c_2232])).

cnf(c_728,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | k2_funct_1(sK6) != sK6
    | u1_struct_0(sK5) != u1_struct_0(sK4)
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_694,c_34])).

cnf(c_2237,plain,
    ( k2_funct_1(sK6) != sK6
    | u1_struct_0(sK5) != u1_struct_0(sK4)
    | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_4281,plain,
    ( k2_funct_1(sK6) != sK6
    | u1_struct_0(sK5) != k1_relat_1(sK6)
    | k2_relat_1(k2_funct_1(sK6)) != k1_relat_1(sK6)
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_relat_1(sK6)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4272,c_2237])).

cnf(c_3939,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2243,c_2248])).

cnf(c_4276,plain,
    ( k2_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6) = k2_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_4272,c_3939])).

cnf(c_4043,plain,
    ( sK0(X0,X1) = X0
    | k1_zfmisc_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_tarski(X0,sK0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2253,c_2256])).

cnf(c_3957,plain,
    ( u1_struct_0(sK3(X0)) = u1_struct_0(X0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3(X0))) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_2256])).

cnf(c_23,plain,
    ( r2_hidden(sK2(X0),X0)
    | k3_tarski(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2246,plain,
    ( k3_tarski(X0) = k1_xboole_0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3487,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = k1_xboole_0
    | r1_tarski(sK2(k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2246,c_2251])).

cnf(c_3488,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(sK2(k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3487,c_8])).

cnf(c_3956,plain,
    ( sK2(k1_zfmisc_1(X0)) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK2(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3488,c_2256])).

cnf(c_2250,plain,
    ( v1_xboole_0(sK1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2257,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3402,plain,
    ( sK1(X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2250,c_2257])).

cnf(c_10,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2249,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3601,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3402,c_2249])).

cnf(c_3941,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3601,c_2248])).

cnf(c_3602,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3402,c_2250])).

cnf(c_811,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
    | u1_struct_0(sK4) != k1_xboole_0
    | k1_relat_1(X0) = X1
    | sK6 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_607,c_777])).

cnf(c_812,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
    | u1_struct_0(sK4) != k1_xboole_0
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_811])).

cnf(c_1479,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_812])).

cnf(c_2236,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1479])).

cnf(c_2228,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK3(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1074])).

cnf(c_2244,plain,
    ( l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2242,plain,
    ( l1_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2241,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2240,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2239,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_24,plain,
    ( sK2(X0) != k1_xboole_0
    | k3_tarski(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:55:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.59/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/0.97  
% 2.59/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/0.97  
% 2.59/0.97  ------  iProver source info
% 2.59/0.97  
% 2.59/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.59/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/0.97  git: non_committed_changes: false
% 2.59/0.97  git: last_make_outside_of_git: false
% 2.59/0.97  
% 2.59/0.97  ------ 
% 2.59/0.97  
% 2.59/0.97  ------ Input Options
% 2.59/0.97  
% 2.59/0.97  --out_options                           all
% 2.59/0.97  --tptp_safe_out                         true
% 2.59/0.97  --problem_path                          ""
% 2.59/0.97  --include_path                          ""
% 2.59/0.97  --clausifier                            res/vclausify_rel
% 2.59/0.97  --clausifier_options                    --mode clausify
% 2.59/0.97  --stdin                                 false
% 2.59/0.97  --stats_out                             all
% 2.59/0.97  
% 2.59/0.97  ------ General Options
% 2.59/0.97  
% 2.59/0.97  --fof                                   false
% 2.59/0.97  --time_out_real                         305.
% 2.59/0.97  --time_out_virtual                      -1.
% 2.59/0.97  --symbol_type_check                     false
% 2.59/0.97  --clausify_out                          false
% 2.59/0.97  --sig_cnt_out                           false
% 2.59/0.97  --trig_cnt_out                          false
% 2.59/0.97  --trig_cnt_out_tolerance                1.
% 2.59/0.97  --trig_cnt_out_sk_spl                   false
% 2.59/0.97  --abstr_cl_out                          false
% 2.59/0.97  
% 2.59/0.97  ------ Global Options
% 2.59/0.97  
% 2.59/0.97  --schedule                              default
% 2.59/0.97  --add_important_lit                     false
% 2.59/0.97  --prop_solver_per_cl                    1000
% 2.59/0.97  --min_unsat_core                        false
% 2.59/0.97  --soft_assumptions                      false
% 2.59/0.97  --soft_lemma_size                       3
% 2.59/0.97  --prop_impl_unit_size                   0
% 2.59/0.97  --prop_impl_unit                        []
% 2.59/0.97  --share_sel_clauses                     true
% 2.59/0.97  --reset_solvers                         false
% 2.59/0.97  --bc_imp_inh                            [conj_cone]
% 2.59/0.97  --conj_cone_tolerance                   3.
% 2.59/0.97  --extra_neg_conj                        none
% 2.59/0.97  --large_theory_mode                     true
% 2.59/0.97  --prolific_symb_bound                   200
% 2.59/0.97  --lt_threshold                          2000
% 2.59/0.97  --clause_weak_htbl                      true
% 2.59/0.97  --gc_record_bc_elim                     false
% 2.59/0.97  
% 2.59/0.97  ------ Preprocessing Options
% 2.59/0.97  
% 2.59/0.97  --preprocessing_flag                    true
% 2.59/0.97  --time_out_prep_mult                    0.1
% 2.59/0.97  --splitting_mode                        input
% 2.59/0.97  --splitting_grd                         true
% 2.59/0.97  --splitting_cvd                         false
% 2.59/0.97  --splitting_cvd_svl                     false
% 2.59/0.97  --splitting_nvd                         32
% 2.59/0.97  --sub_typing                            true
% 2.59/0.97  --prep_gs_sim                           true
% 2.59/0.97  --prep_unflatten                        true
% 2.59/0.97  --prep_res_sim                          true
% 2.59/0.97  --prep_upred                            true
% 2.59/0.97  --prep_sem_filter                       exhaustive
% 2.59/0.97  --prep_sem_filter_out                   false
% 2.59/0.97  --pred_elim                             true
% 2.59/0.97  --res_sim_input                         true
% 2.59/0.97  --eq_ax_congr_red                       true
% 2.59/0.97  --pure_diseq_elim                       true
% 2.59/0.97  --brand_transform                       false
% 2.59/0.97  --non_eq_to_eq                          false
% 2.59/0.97  --prep_def_merge                        true
% 2.59/0.97  --prep_def_merge_prop_impl              false
% 2.59/0.97  --prep_def_merge_mbd                    true
% 2.59/0.97  --prep_def_merge_tr_red                 false
% 2.59/0.97  --prep_def_merge_tr_cl                  false
% 2.59/0.97  --smt_preprocessing                     true
% 2.59/0.97  --smt_ac_axioms                         fast
% 2.59/0.97  --preprocessed_out                      false
% 2.59/0.97  --preprocessed_stats                    false
% 2.59/0.97  
% 2.59/0.97  ------ Abstraction refinement Options
% 2.59/0.97  
% 2.59/0.97  --abstr_ref                             []
% 2.59/0.97  --abstr_ref_prep                        false
% 2.59/0.97  --abstr_ref_until_sat                   false
% 2.59/0.97  --abstr_ref_sig_restrict                funpre
% 2.59/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.97  --abstr_ref_under                       []
% 2.59/0.97  
% 2.59/0.97  ------ SAT Options
% 2.59/0.97  
% 2.59/0.97  --sat_mode                              false
% 2.59/0.97  --sat_fm_restart_options                ""
% 2.59/0.97  --sat_gr_def                            false
% 2.59/0.97  --sat_epr_types                         true
% 2.59/0.97  --sat_non_cyclic_types                  false
% 2.59/0.97  --sat_finite_models                     false
% 2.59/0.97  --sat_fm_lemmas                         false
% 2.59/0.97  --sat_fm_prep                           false
% 2.59/0.97  --sat_fm_uc_incr                        true
% 2.59/0.97  --sat_out_model                         small
% 2.59/0.97  --sat_out_clauses                       false
% 2.59/0.97  
% 2.59/0.97  ------ QBF Options
% 2.59/0.97  
% 2.59/0.97  --qbf_mode                              false
% 2.59/0.97  --qbf_elim_univ                         false
% 2.59/0.97  --qbf_dom_inst                          none
% 2.59/0.97  --qbf_dom_pre_inst                      false
% 2.59/0.97  --qbf_sk_in                             false
% 2.59/0.97  --qbf_pred_elim                         true
% 2.59/0.97  --qbf_split                             512
% 2.59/0.97  
% 2.59/0.97  ------ BMC1 Options
% 2.59/0.97  
% 2.59/0.97  --bmc1_incremental                      false
% 2.59/0.97  --bmc1_axioms                           reachable_all
% 2.59/0.97  --bmc1_min_bound                        0
% 2.59/0.97  --bmc1_max_bound                        -1
% 2.59/0.97  --bmc1_max_bound_default                -1
% 2.59/0.97  --bmc1_symbol_reachability              true
% 2.59/0.97  --bmc1_property_lemmas                  false
% 2.59/0.97  --bmc1_k_induction                      false
% 2.59/0.97  --bmc1_non_equiv_states                 false
% 2.59/0.97  --bmc1_deadlock                         false
% 2.59/0.97  --bmc1_ucm                              false
% 2.59/0.97  --bmc1_add_unsat_core                   none
% 2.59/0.98  --bmc1_unsat_core_children              false
% 2.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.98  --bmc1_out_stat                         full
% 2.59/0.98  --bmc1_ground_init                      false
% 2.59/0.98  --bmc1_pre_inst_next_state              false
% 2.59/0.98  --bmc1_pre_inst_state                   false
% 2.59/0.98  --bmc1_pre_inst_reach_state             false
% 2.59/0.98  --bmc1_out_unsat_core                   false
% 2.59/0.98  --bmc1_aig_witness_out                  false
% 2.59/0.98  --bmc1_verbose                          false
% 2.59/0.98  --bmc1_dump_clauses_tptp                false
% 2.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.98  --bmc1_dump_file                        -
% 2.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.98  --bmc1_ucm_extend_mode                  1
% 2.59/0.98  --bmc1_ucm_init_mode                    2
% 2.59/0.98  --bmc1_ucm_cone_mode                    none
% 2.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.98  --bmc1_ucm_relax_model                  4
% 2.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.98  --bmc1_ucm_layered_model                none
% 2.59/0.98  --bmc1_ucm_max_lemma_size               10
% 2.59/0.98  
% 2.59/0.98  ------ AIG Options
% 2.59/0.98  
% 2.59/0.98  --aig_mode                              false
% 2.59/0.98  
% 2.59/0.98  ------ Instantiation Options
% 2.59/0.98  
% 2.59/0.98  --instantiation_flag                    true
% 2.59/0.98  --inst_sos_flag                         false
% 2.59/0.98  --inst_sos_phase                        true
% 2.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.98  --inst_lit_sel_side                     num_symb
% 2.59/0.98  --inst_solver_per_active                1400
% 2.59/0.98  --inst_solver_calls_frac                1.
% 2.59/0.98  --inst_passive_queue_type               priority_queues
% 2.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.98  --inst_passive_queues_freq              [25;2]
% 2.59/0.98  --inst_dismatching                      true
% 2.59/0.98  --inst_eager_unprocessed_to_passive     true
% 2.59/0.98  --inst_prop_sim_given                   true
% 2.59/0.98  --inst_prop_sim_new                     false
% 2.59/0.98  --inst_subs_new                         false
% 2.59/0.98  --inst_eq_res_simp                      false
% 2.59/0.98  --inst_subs_given                       false
% 2.59/0.98  --inst_orphan_elimination               true
% 2.59/0.98  --inst_learning_loop_flag               true
% 2.59/0.98  --inst_learning_start                   3000
% 2.59/0.98  --inst_learning_factor                  2
% 2.59/0.98  --inst_start_prop_sim_after_learn       3
% 2.59/0.98  --inst_sel_renew                        solver
% 2.59/0.98  --inst_lit_activity_flag                true
% 2.59/0.98  --inst_restr_to_given                   false
% 2.59/0.98  --inst_activity_threshold               500
% 2.59/0.98  --inst_out_proof                        true
% 2.59/0.98  
% 2.59/0.98  ------ Resolution Options
% 2.59/0.98  
% 2.59/0.98  --resolution_flag                       true
% 2.59/0.98  --res_lit_sel                           adaptive
% 2.59/0.98  --res_lit_sel_side                      none
% 2.59/0.98  --res_ordering                          kbo
% 2.59/0.98  --res_to_prop_solver                    active
% 2.59/0.98  --res_prop_simpl_new                    false
% 2.59/0.98  --res_prop_simpl_given                  true
% 2.59/0.98  --res_passive_queue_type                priority_queues
% 2.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.98  --res_passive_queues_freq               [15;5]
% 2.59/0.98  --res_forward_subs                      full
% 2.59/0.98  --res_backward_subs                     full
% 2.59/0.98  --res_forward_subs_resolution           true
% 2.59/0.98  --res_backward_subs_resolution          true
% 2.59/0.98  --res_orphan_elimination                true
% 2.59/0.98  --res_time_limit                        2.
% 2.59/0.98  --res_out_proof                         true
% 2.59/0.98  
% 2.59/0.98  ------ Superposition Options
% 2.59/0.98  
% 2.59/0.98  --superposition_flag                    true
% 2.59/0.98  --sup_passive_queue_type                priority_queues
% 2.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.98  --demod_completeness_check              fast
% 2.59/0.98  --demod_use_ground                      true
% 2.59/0.98  --sup_to_prop_solver                    passive
% 2.59/0.98  --sup_prop_simpl_new                    true
% 2.59/0.98  --sup_prop_simpl_given                  true
% 2.59/0.98  --sup_fun_splitting                     false
% 2.59/0.98  --sup_smt_interval                      50000
% 2.59/0.98  
% 2.59/0.98  ------ Superposition Simplification Setup
% 2.59/0.98  
% 2.59/0.98  --sup_indices_passive                   []
% 2.59/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.98  --sup_full_bw                           [BwDemod]
% 2.59/0.98  --sup_immed_triv                        [TrivRules]
% 2.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.98  --sup_immed_bw_main                     []
% 2.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.98  
% 2.59/0.98  ------ Combination Options
% 2.59/0.98  
% 2.59/0.98  --comb_res_mult                         3
% 2.59/0.98  --comb_sup_mult                         2
% 2.59/0.98  --comb_inst_mult                        10
% 2.59/0.98  
% 2.59/0.98  ------ Debug Options
% 2.59/0.98  
% 2.59/0.98  --dbg_backtrace                         false
% 2.59/0.98  --dbg_dump_prop_clauses                 false
% 2.59/0.98  --dbg_dump_prop_clauses_file            -
% 2.59/0.98  --dbg_out_stat                          false
% 2.59/0.98  ------ Parsing...
% 2.59/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/0.98  
% 2.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.59/0.98  
% 2.59/0.98  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/0.98  
% 2.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.59/0.98  ------ Proving...
% 2.59/0.98  ------ Problem Properties 
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  clauses                                 33
% 2.59/0.98  conjectures                             5
% 2.59/0.98  EPR                                     7
% 2.59/0.98  Horn                                    26
% 2.59/0.98  unary                                   9
% 2.59/0.98  binary                                  9
% 2.59/0.98  lits                                    81
% 2.59/0.98  lits eq                                 25
% 2.59/0.98  fd_pure                                 0
% 2.59/0.98  fd_pseudo                               0
% 2.59/0.98  fd_cond                                 2
% 2.59/0.98  fd_pseudo_cond                          3
% 2.59/0.98  AC symbols                              0
% 2.59/0.98  
% 2.59/0.98  ------ Schedule dynamic 5 is on 
% 2.59/0.98  
% 2.59/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  ------ 
% 2.59/0.98  Current options:
% 2.59/0.98  ------ 
% 2.59/0.98  
% 2.59/0.98  ------ Input Options
% 2.59/0.98  
% 2.59/0.98  --out_options                           all
% 2.59/0.98  --tptp_safe_out                         true
% 2.59/0.98  --problem_path                          ""
% 2.59/0.98  --include_path                          ""
% 2.59/0.98  --clausifier                            res/vclausify_rel
% 2.59/0.98  --clausifier_options                    --mode clausify
% 2.59/0.98  --stdin                                 false
% 2.59/0.98  --stats_out                             all
% 2.59/0.98  
% 2.59/0.98  ------ General Options
% 2.59/0.98  
% 2.59/0.98  --fof                                   false
% 2.59/0.98  --time_out_real                         305.
% 2.59/0.98  --time_out_virtual                      -1.
% 2.59/0.98  --symbol_type_check                     false
% 2.59/0.98  --clausify_out                          false
% 2.59/0.98  --sig_cnt_out                           false
% 2.59/0.98  --trig_cnt_out                          false
% 2.59/0.98  --trig_cnt_out_tolerance                1.
% 2.59/0.98  --trig_cnt_out_sk_spl                   false
% 2.59/0.98  --abstr_cl_out                          false
% 2.59/0.98  
% 2.59/0.98  ------ Global Options
% 2.59/0.98  
% 2.59/0.98  --schedule                              default
% 2.59/0.98  --add_important_lit                     false
% 2.59/0.98  --prop_solver_per_cl                    1000
% 2.59/0.98  --min_unsat_core                        false
% 2.59/0.98  --soft_assumptions                      false
% 2.59/0.98  --soft_lemma_size                       3
% 2.59/0.98  --prop_impl_unit_size                   0
% 2.59/0.98  --prop_impl_unit                        []
% 2.59/0.98  --share_sel_clauses                     true
% 2.59/0.98  --reset_solvers                         false
% 2.59/0.98  --bc_imp_inh                            [conj_cone]
% 2.59/0.98  --conj_cone_tolerance                   3.
% 2.59/0.98  --extra_neg_conj                        none
% 2.59/0.98  --large_theory_mode                     true
% 2.59/0.98  --prolific_symb_bound                   200
% 2.59/0.98  --lt_threshold                          2000
% 2.59/0.98  --clause_weak_htbl                      true
% 2.59/0.98  --gc_record_bc_elim                     false
% 2.59/0.98  
% 2.59/0.98  ------ Preprocessing Options
% 2.59/0.98  
% 2.59/0.98  --preprocessing_flag                    true
% 2.59/0.98  --time_out_prep_mult                    0.1
% 2.59/0.98  --splitting_mode                        input
% 2.59/0.98  --splitting_grd                         true
% 2.59/0.98  --splitting_cvd                         false
% 2.59/0.98  --splitting_cvd_svl                     false
% 2.59/0.98  --splitting_nvd                         32
% 2.59/0.98  --sub_typing                            true
% 2.59/0.98  --prep_gs_sim                           true
% 2.59/0.98  --prep_unflatten                        true
% 2.59/0.98  --prep_res_sim                          true
% 2.59/0.98  --prep_upred                            true
% 2.59/0.98  --prep_sem_filter                       exhaustive
% 2.59/0.98  --prep_sem_filter_out                   false
% 2.59/0.98  --pred_elim                             true
% 2.59/0.98  --res_sim_input                         true
% 2.59/0.98  --eq_ax_congr_red                       true
% 2.59/0.98  --pure_diseq_elim                       true
% 2.59/0.98  --brand_transform                       false
% 2.59/0.98  --non_eq_to_eq                          false
% 2.59/0.98  --prep_def_merge                        true
% 2.59/0.98  --prep_def_merge_prop_impl              false
% 2.59/0.98  --prep_def_merge_mbd                    true
% 2.59/0.98  --prep_def_merge_tr_red                 false
% 2.59/0.98  --prep_def_merge_tr_cl                  false
% 2.59/0.98  --smt_preprocessing                     true
% 2.59/0.98  --smt_ac_axioms                         fast
% 2.59/0.98  --preprocessed_out                      false
% 2.59/0.98  --preprocessed_stats                    false
% 2.59/0.98  
% 2.59/0.98  ------ Abstraction refinement Options
% 2.59/0.98  
% 2.59/0.98  --abstr_ref                             []
% 2.59/0.98  --abstr_ref_prep                        false
% 2.59/0.98  --abstr_ref_until_sat                   false
% 2.59/0.98  --abstr_ref_sig_restrict                funpre
% 2.59/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.98  --abstr_ref_under                       []
% 2.59/0.98  
% 2.59/0.98  ------ SAT Options
% 2.59/0.98  
% 2.59/0.98  --sat_mode                              false
% 2.59/0.98  --sat_fm_restart_options                ""
% 2.59/0.98  --sat_gr_def                            false
% 2.59/0.98  --sat_epr_types                         true
% 2.59/0.98  --sat_non_cyclic_types                  false
% 2.59/0.98  --sat_finite_models                     false
% 2.59/0.98  --sat_fm_lemmas                         false
% 2.59/0.98  --sat_fm_prep                           false
% 2.59/0.98  --sat_fm_uc_incr                        true
% 2.59/0.98  --sat_out_model                         small
% 2.59/0.98  --sat_out_clauses                       false
% 2.59/0.98  
% 2.59/0.98  ------ QBF Options
% 2.59/0.98  
% 2.59/0.98  --qbf_mode                              false
% 2.59/0.98  --qbf_elim_univ                         false
% 2.59/0.98  --qbf_dom_inst                          none
% 2.59/0.98  --qbf_dom_pre_inst                      false
% 2.59/0.98  --qbf_sk_in                             false
% 2.59/0.98  --qbf_pred_elim                         true
% 2.59/0.98  --qbf_split                             512
% 2.59/0.98  
% 2.59/0.98  ------ BMC1 Options
% 2.59/0.98  
% 2.59/0.98  --bmc1_incremental                      false
% 2.59/0.98  --bmc1_axioms                           reachable_all
% 2.59/0.98  --bmc1_min_bound                        0
% 2.59/0.98  --bmc1_max_bound                        -1
% 2.59/0.98  --bmc1_max_bound_default                -1
% 2.59/0.98  --bmc1_symbol_reachability              true
% 2.59/0.98  --bmc1_property_lemmas                  false
% 2.59/0.98  --bmc1_k_induction                      false
% 2.59/0.98  --bmc1_non_equiv_states                 false
% 2.59/0.98  --bmc1_deadlock                         false
% 2.59/0.98  --bmc1_ucm                              false
% 2.59/0.98  --bmc1_add_unsat_core                   none
% 2.59/0.98  --bmc1_unsat_core_children              false
% 2.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.98  --bmc1_out_stat                         full
% 2.59/0.98  --bmc1_ground_init                      false
% 2.59/0.98  --bmc1_pre_inst_next_state              false
% 2.59/0.98  --bmc1_pre_inst_state                   false
% 2.59/0.98  --bmc1_pre_inst_reach_state             false
% 2.59/0.98  --bmc1_out_unsat_core                   false
% 2.59/0.98  --bmc1_aig_witness_out                  false
% 2.59/0.98  --bmc1_verbose                          false
% 2.59/0.98  --bmc1_dump_clauses_tptp                false
% 2.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.98  --bmc1_dump_file                        -
% 2.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.98  --bmc1_ucm_extend_mode                  1
% 2.59/0.98  --bmc1_ucm_init_mode                    2
% 2.59/0.98  --bmc1_ucm_cone_mode                    none
% 2.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.98  --bmc1_ucm_relax_model                  4
% 2.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.98  --bmc1_ucm_layered_model                none
% 2.59/0.98  --bmc1_ucm_max_lemma_size               10
% 2.59/0.98  
% 2.59/0.98  ------ AIG Options
% 2.59/0.98  
% 2.59/0.98  --aig_mode                              false
% 2.59/0.98  
% 2.59/0.98  ------ Instantiation Options
% 2.59/0.98  
% 2.59/0.98  --instantiation_flag                    true
% 2.59/0.98  --inst_sos_flag                         false
% 2.59/0.98  --inst_sos_phase                        true
% 2.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.98  --inst_lit_sel_side                     none
% 2.59/0.98  --inst_solver_per_active                1400
% 2.59/0.98  --inst_solver_calls_frac                1.
% 2.59/0.98  --inst_passive_queue_type               priority_queues
% 2.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.98  --inst_passive_queues_freq              [25;2]
% 2.59/0.98  --inst_dismatching                      true
% 2.59/0.98  --inst_eager_unprocessed_to_passive     true
% 2.59/0.98  --inst_prop_sim_given                   true
% 2.59/0.98  --inst_prop_sim_new                     false
% 2.59/0.98  --inst_subs_new                         false
% 2.59/0.98  --inst_eq_res_simp                      false
% 2.59/0.98  --inst_subs_given                       false
% 2.59/0.98  --inst_orphan_elimination               true
% 2.59/0.98  --inst_learning_loop_flag               true
% 2.59/0.98  --inst_learning_start                   3000
% 2.59/0.98  --inst_learning_factor                  2
% 2.59/0.98  --inst_start_prop_sim_after_learn       3
% 2.59/0.98  --inst_sel_renew                        solver
% 2.59/0.98  --inst_lit_activity_flag                true
% 2.59/0.98  --inst_restr_to_given                   false
% 2.59/0.98  --inst_activity_threshold               500
% 2.59/0.98  --inst_out_proof                        true
% 2.59/0.98  
% 2.59/0.98  ------ Resolution Options
% 2.59/0.98  
% 2.59/0.98  --resolution_flag                       false
% 2.59/0.98  --res_lit_sel                           adaptive
% 2.59/0.98  --res_lit_sel_side                      none
% 2.59/0.98  --res_ordering                          kbo
% 2.59/0.98  --res_to_prop_solver                    active
% 2.59/0.98  --res_prop_simpl_new                    false
% 2.59/0.98  --res_prop_simpl_given                  true
% 2.59/0.98  --res_passive_queue_type                priority_queues
% 2.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.98  --res_passive_queues_freq               [15;5]
% 2.59/0.98  --res_forward_subs                      full
% 2.59/0.98  --res_backward_subs                     full
% 2.59/0.98  --res_forward_subs_resolution           true
% 2.59/0.98  --res_backward_subs_resolution          true
% 2.59/0.98  --res_orphan_elimination                true
% 2.59/0.98  --res_time_limit                        2.
% 2.59/0.98  --res_out_proof                         true
% 2.59/0.98  
% 2.59/0.98  ------ Superposition Options
% 2.59/0.98  
% 2.59/0.98  --superposition_flag                    true
% 2.59/0.98  --sup_passive_queue_type                priority_queues
% 2.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.98  --demod_completeness_check              fast
% 2.59/0.98  --demod_use_ground                      true
% 2.59/0.98  --sup_to_prop_solver                    passive
% 2.59/0.98  --sup_prop_simpl_new                    true
% 2.59/0.98  --sup_prop_simpl_given                  true
% 2.59/0.98  --sup_fun_splitting                     false
% 2.59/0.98  --sup_smt_interval                      50000
% 2.59/0.98  
% 2.59/0.98  ------ Superposition Simplification Setup
% 2.59/0.98  
% 2.59/0.98  --sup_indices_passive                   []
% 2.59/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.98  --sup_full_bw                           [BwDemod]
% 2.59/0.98  --sup_immed_triv                        [TrivRules]
% 2.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.98  --sup_immed_bw_main                     []
% 2.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.98  
% 2.59/0.98  ------ Combination Options
% 2.59/0.98  
% 2.59/0.98  --comb_res_mult                         3
% 2.59/0.98  --comb_sup_mult                         2
% 2.59/0.98  --comb_inst_mult                        10
% 2.59/0.98  
% 2.59/0.98  ------ Debug Options
% 2.59/0.98  
% 2.59/0.98  --dbg_backtrace                         false
% 2.59/0.98  --dbg_dump_prop_clauses                 false
% 2.59/0.98  --dbg_dump_prop_clauses_file            -
% 2.59/0.98  --dbg_out_stat                          false
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  ------ Proving...
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 2.59/0.98  
% 2.59/0.98  % SZS output start Saturation for theBenchmark.p
% 2.59/0.98  
% 2.59/0.98  fof(f3,axiom,(
% 2.59/0.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f54,plain,(
% 2.59/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.59/0.98    inference(nnf_transformation,[],[f3])).
% 2.59/0.98  
% 2.59/0.98  fof(f55,plain,(
% 2.59/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.59/0.98    inference(rectify,[],[f54])).
% 2.59/0.98  
% 2.59/0.98  fof(f56,plain,(
% 2.59/0.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.59/0.98    introduced(choice_axiom,[])).
% 2.59/0.98  
% 2.59/0.98  fof(f57,plain,(
% 2.59/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f55,f56])).
% 2.59/0.98  
% 2.59/0.98  fof(f77,plain,(
% 2.59/0.98    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f57])).
% 2.59/0.98  
% 2.59/0.98  fof(f75,plain,(
% 2.59/0.98    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.59/0.98    inference(cnf_transformation,[],[f57])).
% 2.59/0.98  
% 2.59/0.98  fof(f114,plain,(
% 2.59/0.98    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.59/0.98    inference(equality_resolution,[],[f75])).
% 2.59/0.98  
% 2.59/0.98  fof(f2,axiom,(
% 2.59/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f52,plain,(
% 2.59/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.59/0.98    inference(nnf_transformation,[],[f2])).
% 2.59/0.98  
% 2.59/0.98  fof(f53,plain,(
% 2.59/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.59/0.98    inference(flattening,[],[f52])).
% 2.59/0.98  
% 2.59/0.98  fof(f74,plain,(
% 2.59/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f53])).
% 2.59/0.98  
% 2.59/0.98  fof(f76,plain,(
% 2.59/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.59/0.98    inference(cnf_transformation,[],[f57])).
% 2.59/0.98  
% 2.59/0.98  fof(f113,plain,(
% 2.59/0.98    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.59/0.98    inference(equality_resolution,[],[f76])).
% 2.59/0.98  
% 2.59/0.98  fof(f4,axiom,(
% 2.59/0.98    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f79,plain,(
% 2.59/0.98    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 2.59/0.98    inference(cnf_transformation,[],[f4])).
% 2.59/0.98  
% 2.59/0.98  fof(f17,axiom,(
% 2.59/0.98    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f23,plain,(
% 2.59/0.98    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 2.59/0.98    inference(rectify,[],[f17])).
% 2.59/0.98  
% 2.59/0.98  fof(f45,plain,(
% 2.59/0.98    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 2.59/0.98    inference(ennf_transformation,[],[f23])).
% 2.59/0.98  
% 2.59/0.98  fof(f61,plain,(
% 2.59/0.98    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)))),
% 2.59/0.98    introduced(choice_axiom,[])).
% 2.59/0.98  
% 2.59/0.98  fof(f62,plain,(
% 2.59/0.98    ! [X0] : (((r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 2.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f61])).
% 2.59/0.98  
% 2.59/0.98  fof(f94,plain,(
% 2.59/0.98    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 2.59/0.98    inference(cnf_transformation,[],[f62])).
% 2.59/0.98  
% 2.59/0.98  fof(f78,plain,(
% 2.59/0.98    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | ~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f57])).
% 2.59/0.98  
% 2.59/0.98  fof(f8,axiom,(
% 2.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f27,plain,(
% 2.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.59/0.98    inference(pure_predicate_removal,[],[f8])).
% 2.59/0.98  
% 2.59/0.98  fof(f32,plain,(
% 2.59/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.98    inference(ennf_transformation,[],[f27])).
% 2.59/0.98  
% 2.59/0.98  fof(f83,plain,(
% 2.59/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/0.98    inference(cnf_transformation,[],[f32])).
% 2.59/0.98  
% 2.59/0.98  fof(f12,axiom,(
% 2.59/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f38,plain,(
% 2.59/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.59/0.98    inference(ennf_transformation,[],[f12])).
% 2.59/0.98  
% 2.59/0.98  fof(f39,plain,(
% 2.59/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.59/0.98    inference(flattening,[],[f38])).
% 2.59/0.98  
% 2.59/0.98  fof(f60,plain,(
% 2.59/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.59/0.98    inference(nnf_transformation,[],[f39])).
% 2.59/0.98  
% 2.59/0.98  fof(f88,plain,(
% 2.59/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f60])).
% 2.59/0.98  
% 2.59/0.98  fof(f7,axiom,(
% 2.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f31,plain,(
% 2.59/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.98    inference(ennf_transformation,[],[f7])).
% 2.59/0.98  
% 2.59/0.98  fof(f82,plain,(
% 2.59/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/0.98    inference(cnf_transformation,[],[f31])).
% 2.59/0.98  
% 2.59/0.98  fof(f21,conjecture,(
% 2.59/0.98    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f22,negated_conjecture,(
% 2.59/0.98    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 2.59/0.98    inference(negated_conjecture,[],[f21])).
% 2.59/0.98  
% 2.59/0.98  fof(f24,plain,(
% 2.59/0.98    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 2.59/0.98    inference(pure_predicate_removal,[],[f22])).
% 2.59/0.98  
% 2.59/0.98  fof(f50,plain,(
% 2.59/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_orders_2(X1) & ~v2_struct_0(X1))) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.59/0.98    inference(ennf_transformation,[],[f24])).
% 2.59/0.98  
% 2.59/0.98  fof(f51,plain,(
% 2.59/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 2.59/0.98    inference(flattening,[],[f50])).
% 2.59/0.98  
% 2.59/0.98  fof(f69,plain,(
% 2.59/0.98    ( ! [X0,X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(sK6),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(sK6))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 2.59/0.98    introduced(choice_axiom,[])).
% 2.59/0.98  
% 2.59/0.98  fof(f68,plain,(
% 2.59/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(sK5),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK5)) & v1_funct_1(X2)) & l1_orders_2(sK5) & ~v2_struct_0(sK5))) )),
% 2.59/0.98    introduced(choice_axiom,[])).
% 2.59/0.98  
% 2.59/0.98  fof(f67,plain,(
% 2.59/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK4) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK4)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(sK4) & ~v2_struct_0(sK4))),
% 2.59/0.98    introduced(choice_axiom,[])).
% 2.59/0.98  
% 2.59/0.98  fof(f70,plain,(
% 2.59/0.98    (((k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) | ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_funct_1(sK6))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK6)) & l1_orders_2(sK5) & ~v2_struct_0(sK5)) & l1_orders_2(sK4) & ~v2_struct_0(sK4)),
% 2.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f51,f69,f68,f67])).
% 2.59/0.98  
% 2.59/0.98  fof(f108,plain,(
% 2.59/0.98    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))),
% 2.59/0.98    inference(cnf_transformation,[],[f70])).
% 2.59/0.98  
% 2.59/0.98  fof(f13,axiom,(
% 2.59/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f40,plain,(
% 2.59/0.98    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.59/0.98    inference(ennf_transformation,[],[f13])).
% 2.59/0.98  
% 2.59/0.98  fof(f41,plain,(
% 2.59/0.98    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.59/0.98    inference(flattening,[],[f40])).
% 2.59/0.98  
% 2.59/0.98  fof(f90,plain,(
% 2.59/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f41])).
% 2.59/0.98  
% 2.59/0.98  fof(f107,plain,(
% 2.59/0.98    v1_funct_1(sK6)),
% 2.59/0.98    inference(cnf_transformation,[],[f70])).
% 2.59/0.98  
% 2.59/0.98  fof(f109,plain,(
% 2.59/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 2.59/0.98    inference(cnf_transformation,[],[f70])).
% 2.59/0.98  
% 2.59/0.98  fof(f18,axiom,(
% 2.59/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f46,plain,(
% 2.59/0.98    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 2.59/0.98    inference(ennf_transformation,[],[f18])).
% 2.59/0.98  
% 2.59/0.98  fof(f63,plain,(
% 2.59/0.98    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 2.59/0.98    inference(nnf_transformation,[],[f46])).
% 2.59/0.98  
% 2.59/0.98  fof(f64,plain,(
% 2.59/0.98    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 2.59/0.98    inference(flattening,[],[f63])).
% 2.59/0.98  
% 2.59/0.98  fof(f97,plain,(
% 2.59/0.98    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f64])).
% 2.59/0.98  
% 2.59/0.98  fof(f19,axiom,(
% 2.59/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => l1_orders_2(X1)))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f47,plain,(
% 2.59/0.98    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 2.59/0.98    inference(ennf_transformation,[],[f19])).
% 2.59/0.98  
% 2.59/0.98  fof(f100,plain,(
% 2.59/0.98    ( ! [X0,X1] : (l1_orders_2(X1) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f47])).
% 2.59/0.98  
% 2.59/0.98  fof(f20,axiom,(
% 2.59/0.98    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_yellow_0(X1,X0) & v1_orders_2(X1) & ~v2_struct_0(X1) & m1_yellow_0(X1,X0)))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f25,plain,(
% 2.59/0.98    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ? [X1] : (v1_orders_2(X1) & ~v2_struct_0(X1) & m1_yellow_0(X1,X0)))),
% 2.59/0.98    inference(pure_predicate_removal,[],[f20])).
% 2.59/0.98  
% 2.59/0.98  fof(f26,plain,(
% 2.59/0.98    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v2_struct_0(X1) & m1_yellow_0(X1,X0)))),
% 2.59/0.98    inference(pure_predicate_removal,[],[f25])).
% 2.59/0.98  
% 2.59/0.98  fof(f48,plain,(
% 2.59/0.98    ! [X0] : (? [X1] : (~v2_struct_0(X1) & m1_yellow_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.59/0.98    inference(ennf_transformation,[],[f26])).
% 2.59/0.98  
% 2.59/0.98  fof(f49,plain,(
% 2.59/0.98    ! [X0] : (? [X1] : (~v2_struct_0(X1) & m1_yellow_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.59/0.98    inference(flattening,[],[f48])).
% 2.59/0.98  
% 2.59/0.98  fof(f65,plain,(
% 2.59/0.98    ! [X0] : (? [X1] : (~v2_struct_0(X1) & m1_yellow_0(X1,X0)) => (~v2_struct_0(sK3(X0)) & m1_yellow_0(sK3(X0),X0)))),
% 2.59/0.98    introduced(choice_axiom,[])).
% 2.59/0.98  
% 2.59/0.98  fof(f66,plain,(
% 2.59/0.98    ! [X0] : ((~v2_struct_0(sK3(X0)) & m1_yellow_0(sK3(X0),X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f65])).
% 2.59/0.98  
% 2.59/0.98  fof(f101,plain,(
% 2.59/0.98    ( ! [X0] : (m1_yellow_0(sK3(X0),X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f66])).
% 2.59/0.98  
% 2.59/0.98  fof(f105,plain,(
% 2.59/0.98    ~v2_struct_0(sK5)),
% 2.59/0.98    inference(cnf_transformation,[],[f70])).
% 2.59/0.98  
% 2.59/0.98  fof(f106,plain,(
% 2.59/0.98    l1_orders_2(sK5)),
% 2.59/0.98    inference(cnf_transformation,[],[f70])).
% 2.59/0.98  
% 2.59/0.98  fof(f5,axiom,(
% 2.59/0.98    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f58,plain,(
% 2.59/0.98    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 2.59/0.98    introduced(choice_axiom,[])).
% 2.59/0.98  
% 2.59/0.98  fof(f59,plain,(
% 2.59/0.98    ! [X0] : (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 2.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f58])).
% 2.59/0.98  
% 2.59/0.98  fof(f81,plain,(
% 2.59/0.98    ( ! [X0] : (v1_xboole_0(sK1(X0))) )),
% 2.59/0.98    inference(cnf_transformation,[],[f59])).
% 2.59/0.98  
% 2.59/0.98  fof(f1,axiom,(
% 2.59/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f30,plain,(
% 2.59/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.59/0.98    inference(ennf_transformation,[],[f1])).
% 2.59/0.98  
% 2.59/0.98  fof(f71,plain,(
% 2.59/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f30])).
% 2.59/0.98  
% 2.59/0.98  fof(f102,plain,(
% 2.59/0.98    ( ! [X0] : (~v2_struct_0(sK3(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f66])).
% 2.59/0.98  
% 2.59/0.98  fof(f16,axiom,(
% 2.59/0.98    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f44,plain,(
% 2.59/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.59/0.98    inference(ennf_transformation,[],[f16])).
% 2.59/0.98  
% 2.59/0.98  fof(f93,plain,(
% 2.59/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f44])).
% 2.59/0.98  
% 2.59/0.98  fof(f15,axiom,(
% 2.59/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f42,plain,(
% 2.59/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.59/0.98    inference(ennf_transformation,[],[f15])).
% 2.59/0.98  
% 2.59/0.98  fof(f43,plain,(
% 2.59/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.59/0.98    inference(flattening,[],[f42])).
% 2.59/0.98  
% 2.59/0.98  fof(f92,plain,(
% 2.59/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f43])).
% 2.59/0.98  
% 2.59/0.98  fof(f103,plain,(
% 2.59/0.98    ~v2_struct_0(sK4)),
% 2.59/0.98    inference(cnf_transformation,[],[f70])).
% 2.59/0.98  
% 2.59/0.98  fof(f104,plain,(
% 2.59/0.98    l1_orders_2(sK4)),
% 2.59/0.98    inference(cnf_transformation,[],[f70])).
% 2.59/0.98  
% 2.59/0.98  fof(f91,plain,(
% 2.59/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f41])).
% 2.59/0.98  
% 2.59/0.98  fof(f116,plain,(
% 2.59/0.98    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 2.59/0.98    inference(equality_resolution,[],[f91])).
% 2.59/0.98  
% 2.59/0.98  fof(f110,plain,(
% 2.59/0.98    k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) | ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(k2_funct_1(sK6))),
% 2.59/0.98    inference(cnf_transformation,[],[f70])).
% 2.59/0.98  
% 2.59/0.98  fof(f11,axiom,(
% 2.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f36,plain,(
% 2.59/0.98    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.98    inference(ennf_transformation,[],[f11])).
% 2.59/0.98  
% 2.59/0.98  fof(f37,plain,(
% 2.59/0.98    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.98    inference(flattening,[],[f36])).
% 2.59/0.98  
% 2.59/0.98  fof(f87,plain,(
% 2.59/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/0.98    inference(cnf_transformation,[],[f37])).
% 2.59/0.98  
% 2.59/0.98  fof(f72,plain,(
% 2.59/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.59/0.98    inference(cnf_transformation,[],[f53])).
% 2.59/0.98  
% 2.59/0.98  fof(f112,plain,(
% 2.59/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.59/0.98    inference(equality_resolution,[],[f72])).
% 2.59/0.98  
% 2.59/0.98  fof(f10,axiom,(
% 2.59/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f34,plain,(
% 2.59/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.59/0.98    inference(ennf_transformation,[],[f10])).
% 2.59/0.98  
% 2.59/0.98  fof(f35,plain,(
% 2.59/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.59/0.98    inference(flattening,[],[f34])).
% 2.59/0.98  
% 2.59/0.98  fof(f85,plain,(
% 2.59/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 2.59/0.98    inference(cnf_transformation,[],[f35])).
% 2.59/0.98  
% 2.59/0.98  fof(f9,axiom,(
% 2.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.98  
% 2.59/0.98  fof(f33,plain,(
% 2.59/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.98    inference(ennf_transformation,[],[f9])).
% 2.59/0.98  
% 2.59/0.98  fof(f84,plain,(
% 2.59/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/0.98    inference(cnf_transformation,[],[f33])).
% 2.59/0.98  
% 2.59/0.98  fof(f98,plain,(
% 2.59/0.98    ( ! [X0,X1] : (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f64])).
% 2.59/0.98  
% 2.59/0.98  fof(f89,plain,(
% 2.59/0.98    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f60])).
% 2.59/0.98  
% 2.59/0.98  fof(f115,plain,(
% 2.59/0.98    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.59/0.98    inference(equality_resolution,[],[f89])).
% 2.59/0.98  
% 2.59/0.98  fof(f96,plain,(
% 2.59/0.98    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = k3_tarski(X0)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f62])).
% 2.59/0.98  
% 2.59/0.98  fof(f80,plain,(
% 2.59/0.98    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) )),
% 2.59/0.98    inference(cnf_transformation,[],[f59])).
% 2.59/0.98  
% 2.59/0.98  fof(f95,plain,(
% 2.59/0.98    ( ! [X0] : (k1_xboole_0 != sK2(X0) | k1_xboole_0 = k3_tarski(X0)) )),
% 2.59/0.98    inference(cnf_transformation,[],[f62])).
% 2.59/0.98  
% 2.59/0.98  cnf(c_461,plain,
% 2.59/0.98      ( ~ m1_yellow_0(X0,X1) | m1_yellow_0(X2,X1) | X2 != X0 ),
% 2.59/0.98      theory(equality) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_457,plain,
% 2.59/0.98      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 2.59/0.98      theory(equality) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_456,plain,
% 2.59/0.98      ( ~ v1_partfun1(X0,X1) | v1_partfun1(X0,X2) | X2 != X1 ),
% 2.59/0.98      theory(equality) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_455,plain,
% 2.59/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.98      | v1_funct_2(X3,X4,X5)
% 2.59/0.98      | X3 != X0
% 2.59/0.98      | X4 != X1
% 2.59/0.98      | X5 != X2 ),
% 2.59/0.98      theory(equality) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_453,plain,
% 2.59/0.98      ( ~ v4_relat_1(X0,X1) | v4_relat_1(X0,X2) | X2 != X1 ),
% 2.59/0.98      theory(equality) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1481,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5,plain,
% 2.59/0.98      ( r2_hidden(sK0(X0,X1),X1)
% 2.59/0.98      | r1_tarski(sK0(X0,X1),X0)
% 2.59/0.98      | k1_zfmisc_1(X0) = X1 ),
% 2.59/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2253,plain,
% 2.59/0.98      ( k1_zfmisc_1(X0) = X1
% 2.59/0.98      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.59/0.98      | r1_tarski(sK0(X0,X1),X0) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_7,plain,
% 2.59/0.98      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.59/0.98      inference(cnf_transformation,[],[f114]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2251,plain,
% 2.59/0.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.59/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4044,plain,
% 2.59/0.98      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.59/0.98      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) = iProver_top
% 2.59/0.98      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) = iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2253,c_2251]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1,plain,
% 2.59/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.59/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2256,plain,
% 2.59/0.98      ( X0 = X1
% 2.59/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.59/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5346,plain,
% 2.59/0.98      ( sK0(X0,k1_zfmisc_1(X1)) = X0
% 2.59/0.98      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.59/0.98      | r1_tarski(X0,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
% 2.59/0.98      | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) = iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_4044,c_2256]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5341,plain,
% 2.59/0.98      ( sK0(X0,k1_zfmisc_1(X1)) = X1
% 2.59/0.98      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.59/0.98      | r1_tarski(X1,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
% 2.59/0.98      | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0) = iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_4044,c_2256]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_6,plain,
% 2.59/0.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.59/0.98      inference(cnf_transformation,[],[f113]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2252,plain,
% 2.59/0.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.59/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_8,plain,
% 2.59/0.98      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 2.59/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_25,plain,
% 2.59/0.98      ( ~ r2_hidden(X0,X1) | k3_tarski(X1) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.59/0.98      inference(cnf_transformation,[],[f94]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2245,plain,
% 2.59/0.98      ( k3_tarski(X0) != k1_xboole_0
% 2.59/0.98      | k1_xboole_0 = X1
% 2.59/0.98      | r2_hidden(X1,X0) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3665,plain,
% 2.59/0.98      ( k1_xboole_0 != X0
% 2.59/0.98      | k1_xboole_0 = X1
% 2.59/0.98      | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_8,c_2245]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3736,plain,
% 2.59/0.98      ( k1_xboole_0 = X0
% 2.59/0.98      | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.59/0.98      inference(equality_resolution,[status(thm)],[c_3665]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3741,plain,
% 2.59/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2252,c_3736]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4256,plain,
% 2.59/0.98      ( sK0(k1_xboole_0,X0) = k1_xboole_0
% 2.59/0.98      | k1_zfmisc_1(k1_xboole_0) = X0
% 2.59/0.98      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2253,c_3741]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5159,plain,
% 2.59/0.98      ( sK0(k1_xboole_0,k1_zfmisc_1(X0)) = k1_xboole_0
% 2.59/0.98      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 2.59/0.98      | r1_tarski(sK0(k1_xboole_0,k1_zfmisc_1(X0)),X0) = iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_4256,c_2251]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5278,plain,
% 2.59/0.98      ( sK0(k1_xboole_0,k1_zfmisc_1(X0)) = X0
% 2.59/0.98      | sK0(k1_xboole_0,k1_zfmisc_1(X0)) = k1_xboole_0
% 2.59/0.98      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 2.59/0.98      | r1_tarski(X0,sK0(k1_xboole_0,k1_zfmisc_1(X0))) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_5159,c_2256]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4045,plain,
% 2.59/0.98      ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
% 2.59/0.98      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 2.59/0.98      | r1_tarski(sK0(X0,k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2253,c_3736]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4,plain,
% 2.59/0.98      ( ~ r2_hidden(sK0(X0,X1),X1)
% 2.59/0.98      | ~ r1_tarski(sK0(X0,X1),X0)
% 2.59/0.98      | k1_zfmisc_1(X0) = X1 ),
% 2.59/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2254,plain,
% 2.59/0.98      ( k1_zfmisc_1(X0) = X1
% 2.59/0.98      | r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.59/0.98      | r1_tarski(sK0(X0,X1),X0) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4593,plain,
% 2.59/0.98      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.59/0.98      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) != iProver_top
% 2.59/0.98      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2252,c_2254]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5231,plain,
% 2.59/0.98      ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
% 2.59/0.98      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 2.59/0.98      | r1_tarski(sK0(X0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_4045,c_4593]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5214,plain,
% 2.59/0.98      ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = X0
% 2.59/0.98      | sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
% 2.59/0.98      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 2.59/0.98      | r1_tarski(X0,sK0(X0,k1_zfmisc_1(k1_xboole_0))) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_4045,c_2256]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5158,plain,
% 2.59/0.98      ( sK0(k1_xboole_0,X0) = k1_xboole_0
% 2.59/0.98      | k1_zfmisc_1(k1_xboole_0) = X0
% 2.59/0.98      | r1_tarski(sK0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_4256,c_2254]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_12,plain,
% 2.59/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.59/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_18,plain,
% 2.59/0.98      ( ~ v1_partfun1(X0,X1)
% 2.59/0.98      | ~ v4_relat_1(X0,X1)
% 2.59/0.98      | ~ v1_relat_1(X0)
% 2.59/0.98      | k1_relat_1(X0) = X1 ),
% 2.59/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_602,plain,
% 2.59/0.98      ( ~ v1_partfun1(X0,X1)
% 2.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.98      | ~ v1_relat_1(X0)
% 2.59/0.98      | k1_relat_1(X0) = X1 ),
% 2.59/0.98      inference(resolution,[status(thm)],[c_12,c_18]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_11,plain,
% 2.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.59/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_606,plain,
% 2.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.98      | ~ v1_partfun1(X0,X1)
% 2.59/0.98      | k1_relat_1(X0) = X1 ),
% 2.59/0.98      inference(global_propositional_subsumption,
% 2.59/0.98                [status(thm)],
% 2.59/0.98                [c_602,c_18,c_12,c_11]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_607,plain,
% 2.59/0.98      ( ~ v1_partfun1(X0,X1)
% 2.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.98      | k1_relat_1(X0) = X1 ),
% 2.59/0.98      inference(renaming,[status(thm)],[c_606]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_34,negated_conjecture,
% 2.59/0.98      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
% 2.59/0.98      inference(cnf_transformation,[],[f108]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_20,plain,
% 2.59/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.98      | v1_partfun1(X0,X1)
% 2.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.98      | ~ v1_funct_1(X0)
% 2.59/0.98      | k1_xboole_0 = X2 ),
% 2.59/0.98      inference(cnf_transformation,[],[f90]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_35,negated_conjecture,
% 2.59/0.98      ( v1_funct_1(sK6) ),
% 2.59/0.98      inference(cnf_transformation,[],[f107]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_646,plain,
% 2.59/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.59/0.98      | v1_partfun1(X0,X1)
% 2.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.98      | sK6 != X0
% 2.59/0.98      | k1_xboole_0 = X2 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_647,plain,
% 2.59/0.98      ( ~ v1_funct_2(sK6,X0,X1)
% 2.59/0.98      | v1_partfun1(sK6,X0)
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.98      | k1_xboole_0 = X1 ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_646]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_762,plain,
% 2.59/0.98      ( v1_partfun1(sK6,X0)
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.98      | u1_struct_0(sK5) != X1
% 2.59/0.98      | u1_struct_0(sK4) != X0
% 2.59/0.98      | sK6 != sK6
% 2.59/0.98      | k1_xboole_0 = X1 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_647]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_763,plain,
% 2.59/0.98      ( v1_partfun1(sK6,u1_struct_0(sK4))
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 2.59/0.98      | k1_xboole_0 = u1_struct_0(sK5) ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_762]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_33,negated_conjecture,
% 2.59/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
% 2.59/0.98      inference(cnf_transformation,[],[f109]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_765,plain,
% 2.59/0.98      ( v1_partfun1(sK6,u1_struct_0(sK4)) | k1_xboole_0 = u1_struct_0(sK5) ),
% 2.59/0.98      inference(global_propositional_subsumption,[status(thm)],[c_763,c_33]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_829,plain,
% 2.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.98      | u1_struct_0(sK5) = k1_xboole_0
% 2.59/0.98      | u1_struct_0(sK4) != X1
% 2.59/0.98      | k1_relat_1(X0) = X1
% 2.59/0.98      | sK6 != X0 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_607,c_765]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_830,plain,
% 2.59/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0)))
% 2.59/0.98      | u1_struct_0(sK5) = k1_xboole_0
% 2.59/0.98      | k1_relat_1(sK6) = u1_struct_0(sK4) ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_829]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1478,plain,
% 2.59/0.98      ( sP1_iProver_split
% 2.59/0.98      | u1_struct_0(sK5) = k1_xboole_0
% 2.59/0.98      | k1_relat_1(sK6) = u1_struct_0(sK4) ),
% 2.59/0.98      inference(splitting,
% 2.59/0.98                [splitting(split),new_symbols(definition,[])],
% 2.59/0.98                [c_830]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2233,plain,
% 2.59/0.98      ( u1_struct_0(sK5) = k1_xboole_0
% 2.59/0.98      | k1_relat_1(sK6) = u1_struct_0(sK4)
% 2.59/0.98      | sP1_iProver_split = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1478]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2243,plain,
% 2.59/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1477,plain,
% 2.59/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0)))
% 2.59/0.98      | ~ sP1_iProver_split ),
% 2.59/0.98      inference(splitting,
% 2.59/0.98                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.59/0.98                [c_830]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2234,plain,
% 2.59/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) != iProver_top
% 2.59/0.98      | sP1_iProver_split != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1477]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2558,plain,
% 2.59/0.98      ( sP1_iProver_split != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2243,c_2234]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2559,plain,
% 2.59/0.98      ( ~ sP1_iProver_split ),
% 2.59/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2558]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2895,plain,
% 2.59/0.98      ( k1_relat_1(sK6) = u1_struct_0(sK4) | u1_struct_0(sK5) = k1_xboole_0 ),
% 2.59/0.98      inference(global_propositional_subsumption,
% 2.59/0.98                [status(thm)],
% 2.59/0.98                [c_2233,c_1478,c_2559]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2896,plain,
% 2.59/0.98      ( u1_struct_0(sK5) = k1_xboole_0 | k1_relat_1(sK6) = u1_struct_0(sK4) ),
% 2.59/0.98      inference(renaming,[status(thm)],[c_2895]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_28,plain,
% 2.59/0.98      ( ~ m1_yellow_0(X0,X1)
% 2.59/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.59/0.98      | ~ l1_orders_2(X1)
% 2.59/0.98      | ~ l1_orders_2(X0) ),
% 2.59/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_29,plain,
% 2.59/0.98      ( ~ m1_yellow_0(X0,X1) | ~ l1_orders_2(X1) | l1_orders_2(X0) ),
% 2.59/0.98      inference(cnf_transformation,[],[f100]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_220,plain,
% 2.59/0.98      ( ~ l1_orders_2(X1)
% 2.59/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.59/0.98      | ~ m1_yellow_0(X0,X1) ),
% 2.59/0.98      inference(global_propositional_subsumption,[status(thm)],[c_28,c_29]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_221,plain,
% 2.59/0.98      ( ~ m1_yellow_0(X0,X1)
% 2.59/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.59/0.98      | ~ l1_orders_2(X1) ),
% 2.59/0.98      inference(renaming,[status(thm)],[c_220]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_31,plain,
% 2.59/0.98      ( m1_yellow_0(sK3(X0),X0) | ~ l1_orders_2(X0) | v2_struct_0(X0) ),
% 2.59/0.98      inference(cnf_transformation,[],[f101]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1058,plain,
% 2.59/0.98      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.59/0.98      | ~ l1_orders_2(X1)
% 2.59/0.98      | ~ l1_orders_2(X2)
% 2.59/0.98      | v2_struct_0(X2)
% 2.59/0.98      | X2 != X1
% 2.59/0.98      | sK3(X2) != X0 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_221,c_31]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1059,plain,
% 2.59/0.98      ( r1_tarski(u1_struct_0(sK3(X0)),u1_struct_0(X0))
% 2.59/0.98      | ~ l1_orders_2(X0)
% 2.59/0.98      | v2_struct_0(X0) ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_1058]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2229,plain,
% 2.59/0.98      ( r1_tarski(u1_struct_0(sK3(X0)),u1_struct_0(X0)) = iProver_top
% 2.59/0.98      | l1_orders_2(X0) != iProver_top
% 2.59/0.98      | v2_struct_0(X0) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1059]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3867,plain,
% 2.59/0.98      ( u1_struct_0(sK4) = k1_relat_1(sK6)
% 2.59/0.98      | r1_tarski(u1_struct_0(sK3(sK5)),k1_xboole_0) = iProver_top
% 2.59/0.98      | l1_orders_2(sK5) != iProver_top
% 2.59/0.98      | v2_struct_0(sK5) = iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2896,c_2229]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_37,negated_conjecture,
% 2.59/0.98      ( ~ v2_struct_0(sK5) ),
% 2.59/0.98      inference(cnf_transformation,[],[f105]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_42,plain,
% 2.59/0.98      ( v2_struct_0(sK5) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_36,negated_conjecture,
% 2.59/0.98      ( l1_orders_2(sK5) ),
% 2.59/0.98      inference(cnf_transformation,[],[f106]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_43,plain,
% 2.59/0.98      ( l1_orders_2(sK5) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4111,plain,
% 2.59/0.98      ( u1_struct_0(sK4) = k1_relat_1(sK6)
% 2.59/0.98      | r1_tarski(u1_struct_0(sK3(sK5)),k1_xboole_0) = iProver_top ),
% 2.59/0.98      inference(global_propositional_subsumption,
% 2.59/0.98                [status(thm)],
% 2.59/0.98                [c_3867,c_42,c_43]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4258,plain,
% 2.59/0.98      ( u1_struct_0(sK3(sK5)) = k1_xboole_0
% 2.59/0.98      | u1_struct_0(sK4) = k1_relat_1(sK6) ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_4111,c_3741]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_9,plain,
% 2.59/0.98      ( v1_xboole_0(sK1(X0)) ),
% 2.59/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_107,plain,
% 2.59/0.98      ( v1_xboole_0(sK1(k1_xboole_0)) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_0,plain,
% 2.59/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.59/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_499,plain,
% 2.59/0.98      ( sK1(X0) != X1 | k1_xboole_0 = X1 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_500,plain,
% 2.59/0.98      ( k1_xboole_0 = sK1(X0) ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_499]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_501,plain,
% 2.59/0.98      ( k1_xboole_0 = sK1(k1_xboole_0) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_500]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_30,plain,
% 2.59/0.98      ( ~ l1_orders_2(X0) | v2_struct_0(X0) | ~ v2_struct_0(sK3(X0)) ),
% 2.59/0.98      inference(cnf_transformation,[],[f102]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2492,plain,
% 2.59/0.98      ( ~ l1_orders_2(sK5) | ~ v2_struct_0(sK3(sK5)) | v2_struct_0(sK5) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_30]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1073,plain,
% 2.59/0.98      ( ~ l1_orders_2(X0)
% 2.59/0.98      | ~ l1_orders_2(X1)
% 2.59/0.98      | l1_orders_2(X2)
% 2.59/0.98      | v2_struct_0(X1)
% 2.59/0.98      | X1 != X0
% 2.59/0.98      | sK3(X1) != X2 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_31]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1074,plain,
% 2.59/0.98      ( ~ l1_orders_2(X0) | l1_orders_2(sK3(X0)) | v2_struct_0(X0) ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_1073]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2508,plain,
% 2.59/0.98      ( l1_orders_2(sK3(sK5)) | ~ l1_orders_2(sK5) | v2_struct_0(sK5) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_1074]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1484,plain,
% 2.59/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.59/0.98      theory(equality) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2608,plain,
% 2.59/0.98      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK1(X1)) | X0 != sK1(X1) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_1484]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2610,plain,
% 2.59/0.98      ( ~ v1_xboole_0(sK1(k1_xboole_0))
% 2.59/0.98      | v1_xboole_0(k1_xboole_0)
% 2.59/0.98      | k1_xboole_0 != sK1(k1_xboole_0) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_2608]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_22,plain,
% 2.59/0.98      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.59/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_21,plain,
% 2.59/0.98      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.59/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_523,plain,
% 2.59/0.98      ( ~ l1_orders_2(X0) | v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.59/0.98      inference(resolution,[status(thm)],[c_22,c_21]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2629,plain,
% 2.59/0.98      ( ~ l1_orders_2(sK3(sK5))
% 2.59/0.98      | v2_struct_0(sK3(sK5))
% 2.59/0.98      | ~ v1_xboole_0(u1_struct_0(sK3(sK5))) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_523]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3356,plain,
% 2.59/0.98      ( ~ v1_xboole_0(X0)
% 2.59/0.98      | v1_xboole_0(u1_struct_0(sK3(sK5)))
% 2.59/0.98      | u1_struct_0(sK3(sK5)) != X0 ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_1484]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3358,plain,
% 2.59/0.98      ( v1_xboole_0(u1_struct_0(sK3(sK5)))
% 2.59/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 2.59/0.98      | u1_struct_0(sK3(sK5)) != k1_xboole_0 ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_3356]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4272,plain,
% 2.59/0.98      ( u1_struct_0(sK4) = k1_relat_1(sK6) ),
% 2.59/0.98      inference(global_propositional_subsumption,
% 2.59/0.98                [status(thm)],
% 2.59/0.98                [c_4258,c_37,c_36,c_107,c_501,c_2492,c_2508,c_2610,c_2629,
% 2.59/0.98                 c_3358]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4312,plain,
% 2.59/0.98      ( r1_tarski(u1_struct_0(sK3(sK4)),k1_relat_1(sK6)) = iProver_top
% 2.59/0.98      | l1_orders_2(sK4) != iProver_top
% 2.59/0.98      | v2_struct_0(sK4) = iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_4272,c_2229]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_39,negated_conjecture,
% 2.59/0.98      ( ~ v2_struct_0(sK4) ),
% 2.59/0.98      inference(cnf_transformation,[],[f103]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_40,plain,
% 2.59/0.98      ( v2_struct_0(sK4) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_38,negated_conjecture,
% 2.59/0.98      ( l1_orders_2(sK4) ),
% 2.59/0.98      inference(cnf_transformation,[],[f104]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_41,plain,
% 2.59/0.98      ( l1_orders_2(sK4) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5072,plain,
% 2.59/0.98      ( r1_tarski(u1_struct_0(sK3(sK4)),k1_relat_1(sK6)) = iProver_top ),
% 2.59/0.98      inference(global_propositional_subsumption,
% 2.59/0.98                [status(thm)],
% 2.59/0.98                [c_4312,c_40,c_41]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5077,plain,
% 2.59/0.98      ( u1_struct_0(sK3(sK4)) = k1_relat_1(sK6)
% 2.59/0.98      | r1_tarski(k1_relat_1(sK6),u1_struct_0(sK3(sK4))) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_5072,c_2256]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2238,plain,
% 2.59/0.98      ( l1_orders_2(X0) != iProver_top
% 2.59/0.98      | v2_struct_0(X0) = iProver_top
% 2.59/0.98      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4699,plain,
% 2.59/0.98      ( l1_orders_2(sK4) != iProver_top
% 2.59/0.98      | v2_struct_0(sK4) = iProver_top
% 2.59/0.98      | v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_4272,c_2238]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5066,plain,
% 2.59/0.98      ( v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
% 2.59/0.98      inference(global_propositional_subsumption,
% 2.59/0.98                [status(thm)],
% 2.59/0.98                [c_4699,c_40,c_41]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_19,plain,
% 2.59/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.59/0.98      | v1_partfun1(X0,k1_xboole_0)
% 2.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.59/0.98      | ~ v1_funct_1(X0) ),
% 2.59/0.98      inference(cnf_transformation,[],[f116]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_664,plain,
% 2.59/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.59/0.98      | v1_partfun1(X0,k1_xboole_0)
% 2.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.59/0.98      | sK6 != X0 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_665,plain,
% 2.59/0.98      ( ~ v1_funct_2(sK6,k1_xboole_0,X0)
% 2.59/0.98      | v1_partfun1(sK6,k1_xboole_0)
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_664]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_776,plain,
% 2.59/0.98      ( v1_partfun1(sK6,k1_xboole_0)
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.59/0.98      | u1_struct_0(sK5) != X0
% 2.59/0.98      | u1_struct_0(sK4) != k1_xboole_0
% 2.59/0.98      | sK6 != sK6 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_665]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_777,plain,
% 2.59/0.98      ( v1_partfun1(sK6,k1_xboole_0)
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
% 2.59/0.98      | u1_struct_0(sK4) != k1_xboole_0 ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_776]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_32,negated_conjecture,
% 2.59/0.98      ( ~ v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4))
% 2.59/0.98      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | ~ v1_funct_1(k2_funct_1(sK6))
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 2.59/0.98      inference(cnf_transformation,[],[f110]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_694,plain,
% 2.59/0.98      ( ~ v1_funct_2(k2_funct_1(sK6),u1_struct_0(sK5),u1_struct_0(sK4))
% 2.59/0.98      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | k2_funct_1(sK6) != sK6
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_32,c_35]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_15,plain,
% 2.59/0.98      ( v1_funct_2(X0,X1,X2)
% 2.59/0.98      | ~ v1_partfun1(X0,X1)
% 2.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.98      | ~ v1_funct_1(X0) ),
% 2.59/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_679,plain,
% 2.59/0.98      ( v1_funct_2(X0,X1,X2)
% 2.59/0.98      | ~ v1_partfun1(X0,X1)
% 2.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.98      | sK6 != X0 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_35]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_680,plain,
% 2.59/0.98      ( v1_funct_2(sK6,X0,X1)
% 2.59/0.98      | ~ v1_partfun1(sK6,X0)
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_679]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_743,plain,
% 2.59/0.98      ( ~ v1_partfun1(sK6,X0)
% 2.59/0.98      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.59/0.98      | k2_funct_1(sK6) != sK6
% 2.59/0.98      | u1_struct_0(sK5) != X0
% 2.59/0.98      | u1_struct_0(sK4) != X1
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_694,c_680]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_744,plain,
% 2.59/0.98      ( ~ v1_partfun1(sK6,u1_struct_0(sK5))
% 2.59/0.98      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | k2_funct_1(sK6) != sK6
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_743]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_868,plain,
% 2.59/0.98      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
% 2.59/0.98      | k2_funct_1(sK6) != sK6
% 2.59/0.98      | u1_struct_0(sK5) != k1_xboole_0
% 2.59/0.98      | u1_struct_0(sK4) != k1_xboole_0
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
% 2.59/0.98      | sK6 != sK6 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_777,c_744]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1131,plain,
% 2.59/0.98      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
% 2.59/0.98      | k2_funct_1(sK6) != sK6
% 2.59/0.98      | u1_struct_0(sK5) != k1_xboole_0
% 2.59/0.98      | u1_struct_0(sK4) != k1_xboole_0
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 2.59/0.98      inference(equality_resolution_simp,[status(thm)],[c_868]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2227,plain,
% 2.59/0.98      ( k2_funct_1(sK6) != sK6
% 2.59/0.98      | u1_struct_0(sK5) != k1_xboole_0
% 2.59/0.98      | u1_struct_0(sK4) != k1_xboole_0
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
% 2.59/0.98      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top
% 2.59/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top
% 2.59/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5)))) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1131]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4279,plain,
% 2.59/0.98      ( k2_funct_1(sK6) != sK6
% 2.59/0.98      | u1_struct_0(sK5) != k1_xboole_0
% 2.59/0.98      | k1_relat_1(sK6) != k1_xboole_0
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != k1_relat_1(sK6)
% 2.59/0.98      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_relat_1(sK6)))) != iProver_top
% 2.59/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_relat_1(sK6)))) != iProver_top
% 2.59/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5)))) != iProver_top ),
% 2.59/0.98      inference(demodulation,[status(thm)],[c_4272,c_2227]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2502,plain,
% 2.59/0.98      ( ~ l1_orders_2(sK5)
% 2.59/0.98      | v2_struct_0(sK5)
% 2.59/0.98      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_523]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3346,plain,
% 2.59/0.98      ( ~ v1_xboole_0(X0)
% 2.59/0.98      | v1_xboole_0(u1_struct_0(sK5))
% 2.59/0.98      | u1_struct_0(sK5) != X0 ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_1484]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3348,plain,
% 2.59/0.98      ( v1_xboole_0(u1_struct_0(sK5))
% 2.59/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 2.59/0.98      | u1_struct_0(sK5) != k1_xboole_0 ),
% 2.59/0.98      inference(instantiation,[status(thm)],[c_3346]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_5008,plain,
% 2.59/0.98      ( u1_struct_0(sK5) != k1_xboole_0 ),
% 2.59/0.98      inference(global_propositional_subsumption,
% 2.59/0.98                [status(thm)],
% 2.59/0.98                [c_4279,c_37,c_36,c_107,c_501,c_2502,c_2610,c_3348]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f112]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2255,plain,
% 2.59/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4282,plain,
% 2.59/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),u1_struct_0(sK5)))) = iProver_top ),
% 2.59/0.98      inference(demodulation,[status(thm)],[c_4272,c_2243]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_14,plain,
% 2.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.59/0.98      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 2.59/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2247,plain,
% 2.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.59/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 2.59/0.98      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4606,plain,
% 2.59/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) = iProver_top
% 2.59/0.98      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_4282,c_2247]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_13,plain,
% 2.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.59/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2248,plain,
% 2.59/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.59/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4712,plain,
% 2.59/0.98      ( k2_relset_1(k1_relat_1(sK6),X0,sK6) = k2_relat_1(sK6)
% 2.59/0.98      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_4606,c_2248]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4903,plain,
% 2.59/0.98      ( k2_relset_1(k1_relat_1(sK6),k2_relat_1(sK6),sK6) = k2_relat_1(sK6) ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2255,c_4712]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_27,plain,
% 2.59/0.98      ( ~ m1_yellow_0(X0,X1)
% 2.59/0.98      | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 2.59/0.98      | ~ l1_orders_2(X1)
% 2.59/0.98      | ~ l1_orders_2(X0) ),
% 2.59/0.98      inference(cnf_transformation,[],[f98]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_225,plain,
% 2.59/0.98      ( ~ l1_orders_2(X1)
% 2.59/0.98      | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 2.59/0.98      | ~ m1_yellow_0(X0,X1) ),
% 2.59/0.98      inference(global_propositional_subsumption,[status(thm)],[c_27,c_29]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_226,plain,
% 2.59/0.98      ( ~ m1_yellow_0(X0,X1)
% 2.59/0.98      | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 2.59/0.98      | ~ l1_orders_2(X1) ),
% 2.59/0.98      inference(renaming,[status(thm)],[c_225]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1043,plain,
% 2.59/0.98      ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 2.59/0.98      | ~ l1_orders_2(X1)
% 2.59/0.98      | ~ l1_orders_2(X2)
% 2.59/0.98      | v2_struct_0(X2)
% 2.59/0.98      | X2 != X1
% 2.59/0.98      | sK3(X2) != X0 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_226,c_31]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1044,plain,
% 2.59/0.98      ( r1_tarski(u1_orders_2(sK3(X0)),u1_orders_2(X0))
% 2.59/0.98      | ~ l1_orders_2(X0)
% 2.59/0.98      | v2_struct_0(X0) ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_1043]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2230,plain,
% 2.59/0.98      ( r1_tarski(u1_orders_2(sK3(X0)),u1_orders_2(X0)) = iProver_top
% 2.59/0.98      | l1_orders_2(X0) != iProver_top
% 2.59/0.98      | v2_struct_0(X0) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1044]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4455,plain,
% 2.59/0.98      ( u1_orders_2(sK3(X0)) = u1_orders_2(X0)
% 2.59/0.98      | r1_tarski(u1_orders_2(X0),u1_orders_2(sK3(X0))) != iProver_top
% 2.59/0.98      | l1_orders_2(X0) != iProver_top
% 2.59/0.98      | v2_struct_0(X0) = iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2230,c_2256]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_17,plain,
% 2.59/0.98      ( v1_partfun1(X0,k1_relat_1(X0))
% 2.59/0.98      | ~ v4_relat_1(X0,k1_relat_1(X0))
% 2.59/0.98      | ~ v1_relat_1(X0) ),
% 2.59/0.98      inference(cnf_transformation,[],[f115]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_622,plain,
% 2.59/0.98      ( v1_partfun1(X0,k1_relat_1(X0))
% 2.59/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.59/0.98      | ~ v1_relat_1(X0)
% 2.59/0.98      | X0 != X1
% 2.59/0.98      | k1_relat_1(X0) != X2 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_623,plain,
% 2.59/0.98      ( v1_partfun1(X0,k1_relat_1(X0))
% 2.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.59/0.98      | ~ v1_relat_1(X0) ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_622]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_633,plain,
% 2.59/0.98      ( v1_partfun1(X0,k1_relat_1(X0))
% 2.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ),
% 2.59/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_623,c_11]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_844,plain,
% 2.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.59/0.98      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | k2_funct_1(sK6) != sK6
% 2.59/0.98      | k1_relat_1(X0) != u1_struct_0(sK5)
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
% 2.59/0.98      | sK6 != X0 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_633,c_744]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_845,plain,
% 2.59/0.98      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)))
% 2.59/0.98      | k2_funct_1(sK6) != sK6
% 2.59/0.98      | k1_relat_1(sK6) != u1_struct_0(sK5)
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_844]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1475,plain,
% 2.59/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0)))
% 2.59/0.98      | ~ sP0_iProver_split ),
% 2.59/0.98      inference(splitting,
% 2.59/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.59/0.98                [c_845]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2232,plain,
% 2.59/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),X0))) != iProver_top
% 2.59/0.98      | sP0_iProver_split != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1475]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4447,plain,
% 2.59/0.98      ( sP0_iProver_split != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_4282,c_2232]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_728,plain,
% 2.59/0.98      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 2.59/0.98      | k2_funct_1(sK6) != sK6
% 2.59/0.98      | u1_struct_0(sK5) != u1_struct_0(sK4)
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4) ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_694,c_34]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2237,plain,
% 2.59/0.98      ( k2_funct_1(sK6) != sK6
% 2.59/0.98      | u1_struct_0(sK5) != u1_struct_0(sK4)
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != u1_struct_0(sK4)
% 2.59/0.98      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4281,plain,
% 2.59/0.98      ( k2_funct_1(sK6) != sK6
% 2.59/0.98      | u1_struct_0(sK5) != k1_relat_1(sK6)
% 2.59/0.98      | k2_relat_1(k2_funct_1(sK6)) != k1_relat_1(sK6)
% 2.59/0.98      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_relat_1(sK6)))) != iProver_top ),
% 2.59/0.98      inference(demodulation,[status(thm)],[c_4272,c_2237]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3939,plain,
% 2.59/0.98      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK5),sK6) = k2_relat_1(sK6) ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2243,c_2248]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4276,plain,
% 2.59/0.98      ( k2_relset_1(k1_relat_1(sK6),u1_struct_0(sK5),sK6) = k2_relat_1(sK6) ),
% 2.59/0.98      inference(demodulation,[status(thm)],[c_4272,c_3939]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_4043,plain,
% 2.59/0.98      ( sK0(X0,X1) = X0
% 2.59/0.98      | k1_zfmisc_1(X0) = X1
% 2.59/0.98      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.59/0.98      | r1_tarski(X0,sK0(X0,X1)) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2253,c_2256]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3957,plain,
% 2.59/0.98      ( u1_struct_0(sK3(X0)) = u1_struct_0(X0)
% 2.59/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3(X0))) != iProver_top
% 2.59/0.98      | l1_orders_2(X0) != iProver_top
% 2.59/0.98      | v2_struct_0(X0) = iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2229,c_2256]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_23,plain,
% 2.59/0.98      ( r2_hidden(sK2(X0),X0) | k3_tarski(X0) = k1_xboole_0 ),
% 2.59/0.98      inference(cnf_transformation,[],[f96]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2246,plain,
% 2.59/0.98      ( k3_tarski(X0) = k1_xboole_0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3487,plain,
% 2.59/0.98      ( k3_tarski(k1_zfmisc_1(X0)) = k1_xboole_0
% 2.59/0.98      | r1_tarski(sK2(k1_zfmisc_1(X0)),X0) = iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2246,c_2251]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3488,plain,
% 2.59/0.98      ( k1_xboole_0 = X0 | r1_tarski(sK2(k1_zfmisc_1(X0)),X0) = iProver_top ),
% 2.59/0.98      inference(demodulation,[status(thm)],[c_3487,c_8]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3956,plain,
% 2.59/0.98      ( sK2(k1_zfmisc_1(X0)) = X0
% 2.59/0.98      | k1_xboole_0 = X0
% 2.59/0.98      | r1_tarski(X0,sK2(k1_zfmisc_1(X0))) != iProver_top ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_3488,c_2256]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2250,plain,
% 2.59/0.98      ( v1_xboole_0(sK1(X0)) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2257,plain,
% 2.59/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3402,plain,
% 2.59/0.98      ( sK1(X0) = k1_xboole_0 ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_2250,c_2257]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_10,plain,
% 2.59/0.98      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
% 2.59/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2249,plain,
% 2.59/0.98      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3601,plain,
% 2.59/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.59/0.98      inference(demodulation,[status(thm)],[c_3402,c_2249]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3941,plain,
% 2.59/0.98      ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 2.59/0.98      inference(superposition,[status(thm)],[c_3601,c_2248]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_3602,plain,
% 2.59/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.59/0.98      inference(demodulation,[status(thm)],[c_3402,c_2250]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_811,plain,
% 2.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
% 2.59/0.98      | u1_struct_0(sK4) != k1_xboole_0
% 2.59/0.98      | k1_relat_1(X0) = X1
% 2.59/0.98      | sK6 != X0
% 2.59/0.98      | k1_xboole_0 != X1 ),
% 2.59/0.98      inference(resolution_lifted,[status(thm)],[c_607,c_777]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_812,plain,
% 2.59/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.59/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK5))))
% 2.59/0.98      | u1_struct_0(sK4) != k1_xboole_0
% 2.59/0.98      | k1_relat_1(sK6) = k1_xboole_0 ),
% 2.59/0.98      inference(unflattening,[status(thm)],[c_811]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_1479,plain,
% 2.59/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.59/0.98      | ~ sP2_iProver_split ),
% 2.59/0.98      inference(splitting,
% 2.59/0.98                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.59/0.98                [c_812]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2236,plain,
% 2.59/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 2.59/0.98      | sP2_iProver_split != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1479]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2228,plain,
% 2.59/0.98      ( l1_orders_2(X0) != iProver_top
% 2.59/0.98      | l1_orders_2(sK3(X0)) = iProver_top
% 2.59/0.98      | v2_struct_0(X0) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1074]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2244,plain,
% 2.59/0.98      ( l1_orders_2(X0) != iProver_top
% 2.59/0.98      | v2_struct_0(X0) = iProver_top
% 2.59/0.98      | v2_struct_0(sK3(X0)) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2242,plain,
% 2.59/0.98      ( l1_orders_2(sK5) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2241,plain,
% 2.59/0.98      ( v2_struct_0(sK5) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2240,plain,
% 2.59/0.98      ( l1_orders_2(sK4) = iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_2239,plain,
% 2.59/0.98      ( v2_struct_0(sK4) != iProver_top ),
% 2.59/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.59/0.98  
% 2.59/0.98  cnf(c_24,plain,
% 2.59/0.98      ( sK2(X0) != k1_xboole_0 | k3_tarski(X0) = k1_xboole_0 ),
% 2.59/0.98      inference(cnf_transformation,[],[f95]) ).
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  % SZS output end Saturation for theBenchmark.p
% 2.59/0.98  
% 2.59/0.98  ------                               Statistics
% 2.59/0.98  
% 2.59/0.98  ------ General
% 2.59/0.98  
% 2.59/0.98  abstr_ref_over_cycles:                  0
% 2.59/0.98  abstr_ref_under_cycles:                 0
% 2.59/0.98  gc_basic_clause_elim:                   0
% 2.59/0.98  forced_gc_time:                         0
% 2.59/0.98  parsing_time:                           0.009
% 2.59/0.98  unif_index_cands_time:                  0.
% 2.59/0.98  unif_index_add_time:                    0.
% 2.59/0.98  orderings_time:                         0.
% 2.59/0.98  out_proof_time:                         0.
% 2.59/0.98  total_time:                             0.169
% 2.59/0.98  num_of_symbols:                         64
% 2.59/0.98  num_of_terms:                           4419
% 2.59/0.98  
% 2.59/0.98  ------ Preprocessing
% 2.59/0.98  
% 2.59/0.98  num_of_splits:                          3
% 2.59/0.98  num_of_split_atoms:                     3
% 2.59/0.98  num_of_reused_defs:                     0
% 2.59/0.98  num_eq_ax_congr_red:                    31
% 2.59/0.98  num_of_sem_filtered_clauses:            1
% 2.59/0.98  num_of_subtypes:                        0
% 2.59/0.98  monotx_restored_types:                  0
% 2.59/0.98  sat_num_of_epr_types:                   0
% 2.59/0.98  sat_num_of_non_cyclic_types:            0
% 2.59/0.98  sat_guarded_non_collapsed_types:        0
% 2.59/0.98  num_pure_diseq_elim:                    0
% 2.59/0.98  simp_replaced_by:                       0
% 2.59/0.98  res_preprocessed:                       167
% 2.59/0.98  prep_upred:                             0
% 2.59/0.98  prep_unflattend:                        54
% 2.59/0.98  smt_new_axioms:                         0
% 2.59/0.98  pred_elim_cands:                        6
% 2.59/0.98  pred_elim:                              7
% 2.59/0.98  pred_elim_cl:                           8
% 2.59/0.98  pred_elim_cycles:                       14
% 2.59/0.98  merged_defs:                            8
% 2.59/0.98  merged_defs_ncl:                        0
% 2.59/0.98  bin_hyper_res:                          8
% 2.59/0.98  prep_cycles:                            4
% 2.59/0.98  pred_elim_time:                         0.013
% 2.59/0.98  splitting_time:                         0.
% 2.59/0.98  sem_filter_time:                        0.
% 2.59/0.98  monotx_time:                            0.
% 2.59/0.98  subtype_inf_time:                       0.
% 2.59/0.98  
% 2.59/0.98  ------ Problem properties
% 2.59/0.98  
% 2.59/0.98  clauses:                                33
% 2.59/0.98  conjectures:                            5
% 2.59/0.98  epr:                                    7
% 2.59/0.98  horn:                                   26
% 2.59/0.98  ground:                                 10
% 2.59/0.98  unary:                                  9
% 2.59/0.98  binary:                                 9
% 2.59/0.98  lits:                                   81
% 2.59/0.98  lits_eq:                                25
% 2.59/0.98  fd_pure:                                0
% 2.59/0.98  fd_pseudo:                              0
% 2.59/0.98  fd_cond:                                2
% 2.59/0.98  fd_pseudo_cond:                         3
% 2.59/0.98  ac_symbols:                             0
% 2.59/0.98  
% 2.59/0.98  ------ Propositional Solver
% 2.59/0.98  
% 2.59/0.98  prop_solver_calls:                      27
% 2.59/0.98  prop_fast_solver_calls:                 1174
% 2.59/0.98  smt_solver_calls:                       0
% 2.59/0.98  smt_fast_solver_calls:                  0
% 2.59/0.98  prop_num_of_clauses:                    1992
% 2.59/0.98  prop_preprocess_simplified:             6858
% 2.59/0.98  prop_fo_subsumed:                       22
% 2.59/0.98  prop_solver_time:                       0.
% 2.59/0.98  smt_solver_time:                        0.
% 2.59/0.98  smt_fast_solver_time:                   0.
% 2.59/0.98  prop_fast_solver_time:                  0.
% 2.59/0.98  prop_unsat_core_time:                   0.
% 2.59/0.98  
% 2.59/0.98  ------ QBF
% 2.59/0.98  
% 2.59/0.98  qbf_q_res:                              0
% 2.59/0.98  qbf_num_tautologies:                    0
% 2.59/0.98  qbf_prep_cycles:                        0
% 2.59/0.98  
% 2.59/0.98  ------ BMC1
% 2.59/0.98  
% 2.59/0.98  bmc1_current_bound:                     -1
% 2.59/0.98  bmc1_last_solved_bound:                 -1
% 2.59/0.98  bmc1_unsat_core_size:                   -1
% 2.59/0.98  bmc1_unsat_core_parents_size:           -1
% 2.59/0.98  bmc1_merge_next_fun:                    0
% 2.59/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.59/0.98  
% 2.59/0.98  ------ Instantiation
% 2.59/0.98  
% 2.59/0.98  inst_num_of_clauses:                    602
% 2.59/0.98  inst_num_in_passive:                    97
% 2.59/0.98  inst_num_in_active:                     354
% 2.59/0.98  inst_num_in_unprocessed:                152
% 2.59/0.98  inst_num_of_loops:                      380
% 2.59/0.98  inst_num_of_learning_restarts:          0
% 2.59/0.98  inst_num_moves_active_passive:          24
% 2.59/0.98  inst_lit_activity:                      0
% 2.59/0.98  inst_lit_activity_moves:                0
% 2.59/0.98  inst_num_tautologies:                   0
% 2.59/0.98  inst_num_prop_implied:                  0
% 2.59/0.98  inst_num_existing_simplified:           0
% 2.59/0.98  inst_num_eq_res_simplified:             0
% 2.59/0.98  inst_num_child_elim:                    0
% 2.59/0.98  inst_num_of_dismatching_blockings:      141
% 2.59/0.98  inst_num_of_non_proper_insts:           571
% 2.59/0.98  inst_num_of_duplicates:                 0
% 2.59/0.98  inst_inst_num_from_inst_to_res:         0
% 2.59/0.98  inst_dismatching_checking_time:         0.
% 2.59/0.98  
% 2.59/0.98  ------ Resolution
% 2.59/0.98  
% 2.59/0.98  res_num_of_clauses:                     0
% 2.59/0.98  res_num_in_passive:                     0
% 2.59/0.98  res_num_in_active:                      0
% 2.59/0.98  res_num_of_loops:                       171
% 2.59/0.98  res_forward_subset_subsumed:            30
% 2.59/0.98  res_backward_subset_subsumed:           2
% 2.59/0.98  res_forward_subsumed:                   1
% 2.59/0.98  res_backward_subsumed:                  0
% 2.59/0.98  res_forward_subsumption_resolution:     1
% 2.59/0.98  res_backward_subsumption_resolution:    0
% 2.59/0.98  res_clause_to_clause_subsumption:       251
% 2.59/0.98  res_orphan_elimination:                 0
% 2.59/0.98  res_tautology_del:                      76
% 2.59/0.98  res_num_eq_res_simplified:              1
% 2.59/0.98  res_num_sel_changes:                    0
% 2.59/0.98  res_moves_from_active_to_pass:          0
% 2.59/0.98  
% 2.59/0.98  ------ Superposition
% 2.59/0.98  
% 2.59/0.98  sup_time_total:                         0.
% 2.59/0.98  sup_time_generating:                    0.
% 2.59/0.98  sup_time_sim_full:                      0.
% 2.59/0.98  sup_time_sim_immed:                     0.
% 2.59/0.98  
% 2.59/0.98  sup_num_of_clauses:                     63
% 2.59/0.98  sup_num_in_active:                      61
% 2.59/0.98  sup_num_in_passive:                     2
% 2.59/0.98  sup_num_of_loops:                       74
% 2.59/0.98  sup_fw_superposition:                   36
% 2.59/0.98  sup_bw_superposition:                   36
% 2.59/0.98  sup_immediate_simplified:               14
% 2.59/0.98  sup_given_eliminated:                   0
% 2.59/0.98  comparisons_done:                       0
% 2.59/0.98  comparisons_avoided:                    6
% 2.59/0.98  
% 2.59/0.98  ------ Simplifications
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  sim_fw_subset_subsumed:                 8
% 2.59/0.98  sim_bw_subset_subsumed:                 3
% 2.59/0.98  sim_fw_subsumed:                        4
% 2.59/0.98  sim_bw_subsumed:                        0
% 2.59/0.98  sim_fw_subsumption_res:                 1
% 2.59/0.98  sim_bw_subsumption_res:                 0
% 2.59/0.98  sim_tautology_del:                      5
% 2.59/0.98  sim_eq_tautology_del:                   15
% 2.59/0.98  sim_eq_res_simp:                        0
% 2.59/0.98  sim_fw_demodulated:                     2
% 2.59/0.98  sim_bw_demodulated:                     10
% 2.59/0.98  sim_light_normalised:                   1
% 2.59/0.98  sim_joinable_taut:                      0
% 2.59/0.98  sim_joinable_simp:                      0
% 2.59/0.98  sim_ac_normalised:                      0
% 2.59/0.98  sim_smt_subsumption:                    0
% 2.59/0.98  
%------------------------------------------------------------------------------
