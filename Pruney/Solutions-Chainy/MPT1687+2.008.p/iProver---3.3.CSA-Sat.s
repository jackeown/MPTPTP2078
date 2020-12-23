%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:14 EST 2020

% Result     : CounterSatisfiable 2.70s
% Output     : Saturation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  286 (2378 expanded)
%              Number of clauses        :  182 ( 739 expanded)
%              Number of leaves         :   35 ( 536 expanded)
%              Depth                    :   20
%              Number of atoms          :  953 (13753 expanded)
%              Number of equality atoms :  328 (2128 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f54,plain,(
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

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | r1_tarski(sK0(X0,X1),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f110,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f109,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f4,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f18,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f18])).

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
    inference(ennf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK1(X0),X0)
        & k1_xboole_0 != sK1(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK1(X0),X0)
          & k1_xboole_0 != sK1(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f58])).

fof(f91,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | ~ r1_tarski(sK0(X0,X1),X0)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f25,plain,(
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
    inference(pure_predicate_removal,[],[f23])).

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
    inference(ennf_transformation,[],[f25])).

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

fof(f66,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0)
            | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k2_funct_1(X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(X0)
          | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          | ~ v1_funct_2(k2_funct_1(sK5),u1_struct_0(X1),u1_struct_0(X0))
          | ~ v1_funct_1(k2_funct_1(sK5)) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
              | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
              | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(sK4),u1_struct_0(X0))
              | ~ v1_funct_1(k2_funct_1(X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4))
            & v1_funct_1(X2) )
        & l1_orders_2(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
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
              ( ( k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK3)
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK3))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ( k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3)
      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(k2_funct_1(sK5),u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_funct_1(sK5)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & l1_orders_2(sK4)
    & ~ v2_struct_0(sK4)
    & l1_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f51,f66,f65,f64])).

fof(f105,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f67])).

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

fof(f38,plain,(
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

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f106,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f67])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f60,plain,(
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

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

fof(f97,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_yellow_0(X1,X0)
          & v1_orders_2(X1)
          & ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_orders_2(X1)
          & ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f27,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_yellow_0(X1,X0) )
     => ( ~ v2_struct_0(sK2(X0))
        & m1_yellow_0(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( ~ v2_struct_0(sK2(X0))
        & m1_yellow_0(sK2(X0),X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f62])).

fof(f98,plain,(
    ! [X0] :
      ( m1_yellow_0(sK2(X0),X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f102,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f103,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK2(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f90,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f101,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f93,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f108,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f76,f75])).

fof(f107,plain,
    ( k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3)
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_funct_1(sK5),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f67])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f112,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f85])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f92,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK1(X0)
      | k1_xboole_0 = k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_465,plain,
    ( ~ m1_yellow_0(X0,X1)
    | m1_yellow_0(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_461,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_460,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_459,plain,
    ( ~ v1_partfun1(X0,X1)
    | v1_partfun1(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_457,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_451,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_449,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_2064,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(sK0(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2743,plain,
    ( k1_zfmisc_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_tarski(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2741,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4761,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) = iProver_top
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2743,c_2741])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2739,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2737,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4212,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2739,c_2737])).

cnf(c_5328,plain,
    ( k2_relset_1(X0,X1,sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2))) = k2_relat_1(sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2)))
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)
    | r1_tarski(sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4761,c_4212])).

cnf(c_5661,plain,
    ( k2_relset_1(X0,X1,sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
    | k2_relset_1(X2,X3,sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5328,c_4212])).

cnf(c_5323,plain,
    ( k2_relset_1(X0,X1,sK0(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK0(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)
    | r1_tarski(sK0(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4761,c_4212])).

cnf(c_5586,plain,
    ( k2_relset_1(X0,X1,sK0(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK0(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
    | k2_relset_1(X2,X3,sK0(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK0(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5323,c_4212])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2742,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2735,plain,
    ( k3_tarski(X0) != k1_xboole_0
    | k1_xboole_0 = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4150,plain,
    ( k1_xboole_0 != X0
    | k1_xboole_0 = X1
    | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2735])).

cnf(c_4156,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4150])).

cnf(c_4555,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2742,c_4156])).

cnf(c_4760,plain,
    ( sK0(k1_xboole_0,X0) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2743,c_4555])).

cnf(c_4876,plain,
    ( sK0(k1_xboole_0,k1_zfmisc_1(X0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(sK0(k1_xboole_0,k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4760,c_2741])).

cnf(c_5170,plain,
    ( k2_relset_1(X0,X1,sK0(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK0(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
    | sK0(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4876,c_4212])).

cnf(c_4762,plain,
    ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(sK0(X0,k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2743,c_4156])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r1_tarski(sK0(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2744,plain,
    ( k1_zfmisc_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(sK0(X0,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4791,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) != iProver_top
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2742,c_2744])).

cnf(c_5031,plain,
    ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
    | r1_tarski(sK0(X0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4762,c_4791])).

cnf(c_5030,plain,
    ( k2_relset_1(X0,X1,sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))
    | sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4762,c_4212])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_14,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_555,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_14])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_555,c_14,c_11,c_10])).

cnf(c_560,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_559])).

cnf(c_633,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_16,c_560])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_16,c_560])).

cnf(c_638,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_637])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_710,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_638,c_34])).

cnf(c_711,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(sK5) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_710])).

cnf(c_868,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | u1_struct_0(sK4) != X1
    | u1_struct_0(sK3) != X0
    | k1_relat_1(sK5) = X0
    | sK5 != sK5
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_711])).

cnf(c_869,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | k1_relat_1(sK5) = u1_struct_0(sK3)
    | k1_xboole_0 = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_868])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_871,plain,
    ( k1_relat_1(sK5) = u1_struct_0(sK3)
    | k1_xboole_0 = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_869,c_32])).

cnf(c_27,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_28,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_218,plain,
    ( ~ l1_orders_2(X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_yellow_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_28])).

cnf(c_219,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_218])).

cnf(c_30,plain,
    ( m1_yellow_0(sK2(X0),X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1034,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | X2 != X1
    | sK2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_219,c_30])).

cnf(c_1035,plain,
    ( r1_tarski(u1_struct_0(sK2(X0)),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1034])).

cnf(c_2720,plain,
    ( r1_tarski(u1_struct_0(sK2(X0)),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1035])).

cnf(c_3661,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK5)
    | r1_tarski(u1_struct_0(sK2(sK4)),k1_xboole_0) = iProver_top
    | l1_orders_2(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_871,c_2720])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_41,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_42,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_29,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2943,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v2_struct_0(sK2(sK4))
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2944,plain,
    ( l1_orders_2(sK4) != iProver_top
    | v2_struct_0(sK2(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2943])).

cnf(c_1049,plain,
    ( ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X2)
    | v2_struct_0(X1)
    | X1 != X0
    | sK2(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_1050,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(sK2(X0))
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1049])).

cnf(c_2955,plain,
    ( l1_orders_2(sK2(sK4))
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_2956,plain,
    ( l1_orders_2(sK2(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2955])).

cnf(c_21,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_503,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_504,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_20,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_518,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | u1_struct_0(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_504,c_20])).

cnf(c_519,plain,
    ( ~ r1_tarski(u1_struct_0(X0),k1_xboole_0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_537,plain,
    ( ~ r1_tarski(u1_struct_0(X0),k1_xboole_0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_21,c_519])).

cnf(c_3070,plain,
    ( ~ r1_tarski(u1_struct_0(sK2(sK4)),k1_xboole_0)
    | ~ l1_orders_2(sK2(sK4))
    | v2_struct_0(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_3074,plain,
    ( r1_tarski(u1_struct_0(sK2(sK4)),k1_xboole_0) != iProver_top
    | l1_orders_2(sK2(sK4)) != iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3070])).

cnf(c_3842,plain,
    ( u1_struct_0(sK3) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3661,c_41,c_42,c_2944,c_2956,c_3074])).

cnf(c_2728,plain,
    ( r1_tarski(u1_struct_0(X0),k1_xboole_0) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_4677,plain,
    ( r1_tarski(k1_relat_1(sK5),k1_xboole_0) != iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3842,c_2728])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_39,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_40,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4948,plain,
    ( r1_tarski(k1_relat_1(sK5),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4677,c_39,c_40])).

cnf(c_4875,plain,
    ( sK0(k1_xboole_0,X0) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = X0
    | r1_tarski(sK0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4760,c_2744])).

cnf(c_22,plain,
    ( r2_hidden(sK1(X0),X0)
    | k3_tarski(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2736,plain,
    ( k3_tarski(X0) = k1_xboole_0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3735,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = k1_xboole_0
    | r1_tarski(sK1(k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2736,c_2741])).

cnf(c_3736,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(sK1(k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3735,c_6])).

cnf(c_4854,plain,
    ( k2_relset_1(X0,X1,sK1(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK1(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
    | k2_zfmisc_1(X0,X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3736,c_4212])).

cnf(c_4852,plain,
    ( k2_relset_1(X0,X1,sK0(k2_zfmisc_1(X0,X1),X2)) = k2_relat_1(sK0(k2_zfmisc_1(X0,X1),X2))
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = X2
    | r2_hidden(sK0(k2_zfmisc_1(X0,X1),X2),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2743,c_4212])).

cnf(c_2733,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3849,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3842,c_2733])).

cnf(c_4214,plain,
    ( k2_relset_1(k1_relat_1(sK5),u1_struct_0(sK4),sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3849,c_2737])).

cnf(c_17,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_737,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5))))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_782,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5))))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_737])).

cnf(c_783,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) ),
    inference(unflattening,[status(thm)],[c_782])).

cnf(c_2727,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2940,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_2941,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2940])).

cnf(c_3445,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2727,c_45,c_2941])).

cnf(c_4213,plain,
    ( k2_relset_1(k1_relat_1(sK5),k2_relat_1(sK5),sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3445,c_2737])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2740,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4211,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2740,c_2737])).

cnf(c_3867,plain,
    ( r1_tarski(u1_struct_0(sK2(sK3)),k1_relat_1(sK5)) = iProver_top
    | l1_orders_2(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3842,c_2720])).

cnf(c_4067,plain,
    ( r1_tarski(u1_struct_0(sK2(sK3)),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3867,c_39,c_40])).

cnf(c_31,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK5),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_746,plain,
    ( ~ v1_funct_2(k2_funct_1(sK5),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | k2_funct_1(sK5) != sK5
    | k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_31,c_34])).

cnf(c_812,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | k2_funct_1(sK5) != sK5
    | u1_struct_0(sK4) != u1_struct_0(sK3)
    | k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_746,c_33])).

cnf(c_2726,plain,
    ( k2_funct_1(sK5) != sK5
    | u1_struct_0(sK4) != u1_struct_0(sK3)
    | k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3)
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_3848,plain,
    ( k2_funct_1(sK5) != sK5
    | u1_struct_0(sK4) != k1_relat_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) != k1_relat_1(sK5)
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k1_relat_1(sK5)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3842,c_2726])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_659,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | X0 != X2
    | k1_relat_1(X2) = X3
    | k1_xboole_0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_560,c_15])).

cnf(c_660,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_692,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | k1_relat_1(X0) = k1_xboole_0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_660,c_34])).

cnf(c_693,plain,
    ( ~ v1_funct_2(sK5,k1_xboole_0,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_850,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | u1_struct_0(sK4) != X1
    | u1_struct_0(sK3) != k1_xboole_0
    | k1_relat_1(sK5) = k1_xboole_0
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_693])).

cnf(c_851,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK4))))
    | u1_struct_0(sK3) != k1_xboole_0
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_850])).

cnf(c_2061,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK4))))
    | sP0_iProver_split
    | u1_struct_0(sK3) != k1_xboole_0
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_851])).

cnf(c_2722,plain,
    ( u1_struct_0(sK3) != k1_xboole_0
    | k1_relat_1(sK5) = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK4)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2061])).

cnf(c_2060,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_851])).

cnf(c_2723,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2060])).

cnf(c_2855,plain,
    ( u1_struct_0(sK3) != k1_xboole_0
    | k1_relat_1(sK5) = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK4)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2722,c_2723])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_105,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_111,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_113,plain,
    ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_297,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_298,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_297])).

cnf(c_980,plain,
    ( ~ r1_tarski(X0,X1)
    | X2 != X0
    | k3_tarski(X3) != k1_xboole_0
    | k1_zfmisc_1(X1) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_298,c_24])).

cnf(c_981,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k1_zfmisc_1(X1)) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_980])).

cnf(c_983,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k3_tarski(k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_981])).

cnf(c_2952,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),k1_xboole_0)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_2067,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3056,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(u1_struct_0(sK3),k1_xboole_0)
    | u1_struct_0(sK3) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_2067])).

cnf(c_3058,plain,
    ( r1_tarski(u1_struct_0(sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | u1_struct_0(sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3056])).

cnf(c_3451,plain,
    ( u1_struct_0(sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2855,c_38,c_37,c_105,c_111,c_113,c_983,c_2952,c_3058])).

cnf(c_3847,plain,
    ( k1_relat_1(sK5) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3842,c_3451])).

cnf(c_2738,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3571,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2733,c_2738])).

cnf(c_3845,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3842,c_3571])).

cnf(c_3724,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2739,c_2723])).

cnf(c_3572,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3445,c_2738])).

cnf(c_3570,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2740,c_2738])).

cnf(c_18,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_726,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_727,plain,
    ( v1_funct_2(sK5,k1_relat_1(sK5),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_794,plain,
    ( v1_funct_2(sK5,k1_relat_1(sK5),k2_relat_1(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_727])).

cnf(c_795,plain,
    ( v1_funct_2(sK5,k1_relat_1(sK5),k2_relat_1(sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(unflattening,[status(thm)],[c_794])).

cnf(c_827,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_funct_1(sK5) != sK5
    | u1_struct_0(sK4) != k1_relat_1(sK5)
    | u1_struct_0(sK3) != k2_relat_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_746,c_795])).

cnf(c_2062,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_827])).

cnf(c_2725,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2062])).

cnf(c_3310,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2733,c_2725])).

cnf(c_2719,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1050])).

cnf(c_26,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_223,plain,
    ( ~ l1_orders_2(X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ m1_yellow_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_28])).

cnf(c_224,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_1019,plain,
    ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | X2 != X1
    | sK2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_224,c_30])).

cnf(c_1020,plain,
    ( r1_tarski(u1_orders_2(sK2(X0)),u1_orders_2(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1019])).

cnf(c_2721,plain,
    ( r1_tarski(u1_orders_2(sK2(X0)),u1_orders_2(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_2734,plain,
    ( l1_orders_2(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2732,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2731,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2730,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2729,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_23,plain,
    ( sK1(X0) != k1_xboole_0
    | k3_tarski(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.70/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/0.98  
% 2.70/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/0.98  
% 2.70/0.98  ------  iProver source info
% 2.70/0.98  
% 2.70/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.70/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/0.98  git: non_committed_changes: false
% 2.70/0.98  git: last_make_outside_of_git: false
% 2.70/0.98  
% 2.70/0.98  ------ 
% 2.70/0.98  
% 2.70/0.98  ------ Input Options
% 2.70/0.98  
% 2.70/0.98  --out_options                           all
% 2.70/0.98  --tptp_safe_out                         true
% 2.70/0.98  --problem_path                          ""
% 2.70/0.98  --include_path                          ""
% 2.70/0.98  --clausifier                            res/vclausify_rel
% 2.70/0.98  --clausifier_options                    --mode clausify
% 2.70/0.98  --stdin                                 false
% 2.70/0.98  --stats_out                             all
% 2.70/0.98  
% 2.70/0.98  ------ General Options
% 2.70/0.98  
% 2.70/0.98  --fof                                   false
% 2.70/0.98  --time_out_real                         305.
% 2.70/0.98  --time_out_virtual                      -1.
% 2.70/0.98  --symbol_type_check                     false
% 2.70/0.98  --clausify_out                          false
% 2.70/0.98  --sig_cnt_out                           false
% 2.70/0.98  --trig_cnt_out                          false
% 2.70/0.98  --trig_cnt_out_tolerance                1.
% 2.70/0.98  --trig_cnt_out_sk_spl                   false
% 2.70/0.98  --abstr_cl_out                          false
% 2.70/0.98  
% 2.70/0.98  ------ Global Options
% 2.70/0.98  
% 2.70/0.98  --schedule                              default
% 2.70/0.98  --add_important_lit                     false
% 2.70/0.98  --prop_solver_per_cl                    1000
% 2.70/0.98  --min_unsat_core                        false
% 2.70/0.98  --soft_assumptions                      false
% 2.70/0.98  --soft_lemma_size                       3
% 2.70/0.98  --prop_impl_unit_size                   0
% 2.70/0.98  --prop_impl_unit                        []
% 2.70/0.98  --share_sel_clauses                     true
% 2.70/0.98  --reset_solvers                         false
% 2.70/0.98  --bc_imp_inh                            [conj_cone]
% 2.70/0.98  --conj_cone_tolerance                   3.
% 2.70/0.98  --extra_neg_conj                        none
% 2.70/0.98  --large_theory_mode                     true
% 2.70/0.98  --prolific_symb_bound                   200
% 2.70/0.98  --lt_threshold                          2000
% 2.70/0.98  --clause_weak_htbl                      true
% 2.70/0.98  --gc_record_bc_elim                     false
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing Options
% 2.70/0.98  
% 2.70/0.98  --preprocessing_flag                    true
% 2.70/0.98  --time_out_prep_mult                    0.1
% 2.70/0.98  --splitting_mode                        input
% 2.70/0.98  --splitting_grd                         true
% 2.70/0.98  --splitting_cvd                         false
% 2.70/0.98  --splitting_cvd_svl                     false
% 2.70/0.98  --splitting_nvd                         32
% 2.70/0.98  --sub_typing                            true
% 2.70/0.98  --prep_gs_sim                           true
% 2.70/0.98  --prep_unflatten                        true
% 2.70/0.98  --prep_res_sim                          true
% 2.70/0.98  --prep_upred                            true
% 2.70/0.98  --prep_sem_filter                       exhaustive
% 2.70/0.98  --prep_sem_filter_out                   false
% 2.70/0.98  --pred_elim                             true
% 2.70/0.98  --res_sim_input                         true
% 2.70/0.98  --eq_ax_congr_red                       true
% 2.70/0.98  --pure_diseq_elim                       true
% 2.70/0.98  --brand_transform                       false
% 2.70/0.98  --non_eq_to_eq                          false
% 2.70/0.98  --prep_def_merge                        true
% 2.70/0.98  --prep_def_merge_prop_impl              false
% 2.70/0.98  --prep_def_merge_mbd                    true
% 2.70/0.98  --prep_def_merge_tr_red                 false
% 2.70/0.98  --prep_def_merge_tr_cl                  false
% 2.70/0.98  --smt_preprocessing                     true
% 2.70/0.98  --smt_ac_axioms                         fast
% 2.70/0.98  --preprocessed_out                      false
% 2.70/0.98  --preprocessed_stats                    false
% 2.70/0.98  
% 2.70/0.98  ------ Abstraction refinement Options
% 2.70/0.98  
% 2.70/0.98  --abstr_ref                             []
% 2.70/0.98  --abstr_ref_prep                        false
% 2.70/0.98  --abstr_ref_until_sat                   false
% 2.70/0.98  --abstr_ref_sig_restrict                funpre
% 2.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.98  --abstr_ref_under                       []
% 2.70/0.98  
% 2.70/0.98  ------ SAT Options
% 2.70/0.98  
% 2.70/0.98  --sat_mode                              false
% 2.70/0.98  --sat_fm_restart_options                ""
% 2.70/0.98  --sat_gr_def                            false
% 2.70/0.98  --sat_epr_types                         true
% 2.70/0.98  --sat_non_cyclic_types                  false
% 2.70/0.98  --sat_finite_models                     false
% 2.70/0.98  --sat_fm_lemmas                         false
% 2.70/0.98  --sat_fm_prep                           false
% 2.70/0.98  --sat_fm_uc_incr                        true
% 2.70/0.98  --sat_out_model                         small
% 2.70/0.98  --sat_out_clauses                       false
% 2.70/0.98  
% 2.70/0.98  ------ QBF Options
% 2.70/0.98  
% 2.70/0.98  --qbf_mode                              false
% 2.70/0.98  --qbf_elim_univ                         false
% 2.70/0.98  --qbf_dom_inst                          none
% 2.70/0.98  --qbf_dom_pre_inst                      false
% 2.70/0.98  --qbf_sk_in                             false
% 2.70/0.98  --qbf_pred_elim                         true
% 2.70/0.98  --qbf_split                             512
% 2.70/0.98  
% 2.70/0.98  ------ BMC1 Options
% 2.70/0.98  
% 2.70/0.98  --bmc1_incremental                      false
% 2.70/0.98  --bmc1_axioms                           reachable_all
% 2.70/0.98  --bmc1_min_bound                        0
% 2.70/0.98  --bmc1_max_bound                        -1
% 2.70/0.98  --bmc1_max_bound_default                -1
% 2.70/0.98  --bmc1_symbol_reachability              true
% 2.70/0.98  --bmc1_property_lemmas                  false
% 2.70/0.98  --bmc1_k_induction                      false
% 2.70/0.98  --bmc1_non_equiv_states                 false
% 2.70/0.98  --bmc1_deadlock                         false
% 2.70/0.98  --bmc1_ucm                              false
% 2.70/0.98  --bmc1_add_unsat_core                   none
% 2.70/0.99  --bmc1_unsat_core_children              false
% 2.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.99  --bmc1_out_stat                         full
% 2.70/0.99  --bmc1_ground_init                      false
% 2.70/0.99  --bmc1_pre_inst_next_state              false
% 2.70/0.99  --bmc1_pre_inst_state                   false
% 2.70/0.99  --bmc1_pre_inst_reach_state             false
% 2.70/0.99  --bmc1_out_unsat_core                   false
% 2.70/0.99  --bmc1_aig_witness_out                  false
% 2.70/0.99  --bmc1_verbose                          false
% 2.70/0.99  --bmc1_dump_clauses_tptp                false
% 2.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.99  --bmc1_dump_file                        -
% 2.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.99  --bmc1_ucm_extend_mode                  1
% 2.70/0.99  --bmc1_ucm_init_mode                    2
% 2.70/0.99  --bmc1_ucm_cone_mode                    none
% 2.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.99  --bmc1_ucm_relax_model                  4
% 2.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.99  --bmc1_ucm_layered_model                none
% 2.70/0.99  --bmc1_ucm_max_lemma_size               10
% 2.70/0.99  
% 2.70/0.99  ------ AIG Options
% 2.70/0.99  
% 2.70/0.99  --aig_mode                              false
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation Options
% 2.70/0.99  
% 2.70/0.99  --instantiation_flag                    true
% 2.70/0.99  --inst_sos_flag                         false
% 2.70/0.99  --inst_sos_phase                        true
% 2.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel_side                     num_symb
% 2.70/0.99  --inst_solver_per_active                1400
% 2.70/0.99  --inst_solver_calls_frac                1.
% 2.70/0.99  --inst_passive_queue_type               priority_queues
% 2.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.99  --inst_passive_queues_freq              [25;2]
% 2.70/0.99  --inst_dismatching                      true
% 2.70/0.99  --inst_eager_unprocessed_to_passive     true
% 2.70/0.99  --inst_prop_sim_given                   true
% 2.70/0.99  --inst_prop_sim_new                     false
% 2.70/0.99  --inst_subs_new                         false
% 2.70/0.99  --inst_eq_res_simp                      false
% 2.70/0.99  --inst_subs_given                       false
% 2.70/0.99  --inst_orphan_elimination               true
% 2.70/0.99  --inst_learning_loop_flag               true
% 2.70/0.99  --inst_learning_start                   3000
% 2.70/0.99  --inst_learning_factor                  2
% 2.70/0.99  --inst_start_prop_sim_after_learn       3
% 2.70/0.99  --inst_sel_renew                        solver
% 2.70/0.99  --inst_lit_activity_flag                true
% 2.70/0.99  --inst_restr_to_given                   false
% 2.70/0.99  --inst_activity_threshold               500
% 2.70/0.99  --inst_out_proof                        true
% 2.70/0.99  
% 2.70/0.99  ------ Resolution Options
% 2.70/0.99  
% 2.70/0.99  --resolution_flag                       true
% 2.70/0.99  --res_lit_sel                           adaptive
% 2.70/0.99  --res_lit_sel_side                      none
% 2.70/0.99  --res_ordering                          kbo
% 2.70/0.99  --res_to_prop_solver                    active
% 2.70/0.99  --res_prop_simpl_new                    false
% 2.70/0.99  --res_prop_simpl_given                  true
% 2.70/0.99  --res_passive_queue_type                priority_queues
% 2.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.99  --res_passive_queues_freq               [15;5]
% 2.70/0.99  --res_forward_subs                      full
% 2.70/0.99  --res_backward_subs                     full
% 2.70/0.99  --res_forward_subs_resolution           true
% 2.70/0.99  --res_backward_subs_resolution          true
% 2.70/0.99  --res_orphan_elimination                true
% 2.70/0.99  --res_time_limit                        2.
% 2.70/0.99  --res_out_proof                         true
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Options
% 2.70/0.99  
% 2.70/0.99  --superposition_flag                    true
% 2.70/0.99  --sup_passive_queue_type                priority_queues
% 2.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.99  --demod_completeness_check              fast
% 2.70/0.99  --demod_use_ground                      true
% 2.70/0.99  --sup_to_prop_solver                    passive
% 2.70/0.99  --sup_prop_simpl_new                    true
% 2.70/0.99  --sup_prop_simpl_given                  true
% 2.70/0.99  --sup_fun_splitting                     false
% 2.70/0.99  --sup_smt_interval                      50000
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Simplification Setup
% 2.70/0.99  
% 2.70/0.99  --sup_indices_passive                   []
% 2.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_full_bw                           [BwDemod]
% 2.70/0.99  --sup_immed_triv                        [TrivRules]
% 2.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_immed_bw_main                     []
% 2.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  
% 2.70/0.99  ------ Combination Options
% 2.70/0.99  
% 2.70/0.99  --comb_res_mult                         3
% 2.70/0.99  --comb_sup_mult                         2
% 2.70/0.99  --comb_inst_mult                        10
% 2.70/0.99  
% 2.70/0.99  ------ Debug Options
% 2.70/0.99  
% 2.70/0.99  --dbg_backtrace                         false
% 2.70/0.99  --dbg_dump_prop_clauses                 false
% 2.70/0.99  --dbg_dump_prop_clauses_file            -
% 2.70/0.99  --dbg_out_stat                          false
% 2.70/0.99  ------ Parsing...
% 2.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/0.99  ------ Proving...
% 2.70/0.99  ------ Problem Properties 
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  clauses                                 29
% 2.70/0.99  conjectures                             5
% 2.70/0.99  EPR                                     4
% 2.70/0.99  Horn                                    22
% 2.70/0.99  unary                                   7
% 2.70/0.99  binary                                  11
% 2.70/0.99  lits                                    67
% 2.70/0.99  lits eq                                 20
% 2.70/0.99  fd_pure                                 0
% 2.70/0.99  fd_pseudo                               0
% 2.70/0.99  fd_cond                                 1
% 2.70/0.99  fd_pseudo_cond                          2
% 2.70/0.99  AC symbols                              0
% 2.70/0.99  
% 2.70/0.99  ------ Schedule dynamic 5 is on 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  ------ 
% 2.70/0.99  Current options:
% 2.70/0.99  ------ 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options
% 2.70/0.99  
% 2.70/0.99  --out_options                           all
% 2.70/0.99  --tptp_safe_out                         true
% 2.70/0.99  --problem_path                          ""
% 2.70/0.99  --include_path                          ""
% 2.70/0.99  --clausifier                            res/vclausify_rel
% 2.70/0.99  --clausifier_options                    --mode clausify
% 2.70/0.99  --stdin                                 false
% 2.70/0.99  --stats_out                             all
% 2.70/0.99  
% 2.70/0.99  ------ General Options
% 2.70/0.99  
% 2.70/0.99  --fof                                   false
% 2.70/0.99  --time_out_real                         305.
% 2.70/0.99  --time_out_virtual                      -1.
% 2.70/0.99  --symbol_type_check                     false
% 2.70/0.99  --clausify_out                          false
% 2.70/0.99  --sig_cnt_out                           false
% 2.70/0.99  --trig_cnt_out                          false
% 2.70/0.99  --trig_cnt_out_tolerance                1.
% 2.70/0.99  --trig_cnt_out_sk_spl                   false
% 2.70/0.99  --abstr_cl_out                          false
% 2.70/0.99  
% 2.70/0.99  ------ Global Options
% 2.70/0.99  
% 2.70/0.99  --schedule                              default
% 2.70/0.99  --add_important_lit                     false
% 2.70/0.99  --prop_solver_per_cl                    1000
% 2.70/0.99  --min_unsat_core                        false
% 2.70/0.99  --soft_assumptions                      false
% 2.70/0.99  --soft_lemma_size                       3
% 2.70/0.99  --prop_impl_unit_size                   0
% 2.70/0.99  --prop_impl_unit                        []
% 2.70/0.99  --share_sel_clauses                     true
% 2.70/0.99  --reset_solvers                         false
% 2.70/0.99  --bc_imp_inh                            [conj_cone]
% 2.70/0.99  --conj_cone_tolerance                   3.
% 2.70/0.99  --extra_neg_conj                        none
% 2.70/0.99  --large_theory_mode                     true
% 2.70/0.99  --prolific_symb_bound                   200
% 2.70/0.99  --lt_threshold                          2000
% 2.70/0.99  --clause_weak_htbl                      true
% 2.70/0.99  --gc_record_bc_elim                     false
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing Options
% 2.70/0.99  
% 2.70/0.99  --preprocessing_flag                    true
% 2.70/0.99  --time_out_prep_mult                    0.1
% 2.70/0.99  --splitting_mode                        input
% 2.70/0.99  --splitting_grd                         true
% 2.70/0.99  --splitting_cvd                         false
% 2.70/0.99  --splitting_cvd_svl                     false
% 2.70/0.99  --splitting_nvd                         32
% 2.70/0.99  --sub_typing                            true
% 2.70/0.99  --prep_gs_sim                           true
% 2.70/0.99  --prep_unflatten                        true
% 2.70/0.99  --prep_res_sim                          true
% 2.70/0.99  --prep_upred                            true
% 2.70/0.99  --prep_sem_filter                       exhaustive
% 2.70/0.99  --prep_sem_filter_out                   false
% 2.70/0.99  --pred_elim                             true
% 2.70/0.99  --res_sim_input                         true
% 2.70/0.99  --eq_ax_congr_red                       true
% 2.70/0.99  --pure_diseq_elim                       true
% 2.70/0.99  --brand_transform                       false
% 2.70/0.99  --non_eq_to_eq                          false
% 2.70/0.99  --prep_def_merge                        true
% 2.70/0.99  --prep_def_merge_prop_impl              false
% 2.70/0.99  --prep_def_merge_mbd                    true
% 2.70/0.99  --prep_def_merge_tr_red                 false
% 2.70/0.99  --prep_def_merge_tr_cl                  false
% 2.70/0.99  --smt_preprocessing                     true
% 2.70/0.99  --smt_ac_axioms                         fast
% 2.70/0.99  --preprocessed_out                      false
% 2.70/0.99  --preprocessed_stats                    false
% 2.70/0.99  
% 2.70/0.99  ------ Abstraction refinement Options
% 2.70/0.99  
% 2.70/0.99  --abstr_ref                             []
% 2.70/0.99  --abstr_ref_prep                        false
% 2.70/0.99  --abstr_ref_until_sat                   false
% 2.70/0.99  --abstr_ref_sig_restrict                funpre
% 2.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.99  --abstr_ref_under                       []
% 2.70/0.99  
% 2.70/0.99  ------ SAT Options
% 2.70/0.99  
% 2.70/0.99  --sat_mode                              false
% 2.70/0.99  --sat_fm_restart_options                ""
% 2.70/0.99  --sat_gr_def                            false
% 2.70/0.99  --sat_epr_types                         true
% 2.70/0.99  --sat_non_cyclic_types                  false
% 2.70/0.99  --sat_finite_models                     false
% 2.70/0.99  --sat_fm_lemmas                         false
% 2.70/0.99  --sat_fm_prep                           false
% 2.70/0.99  --sat_fm_uc_incr                        true
% 2.70/0.99  --sat_out_model                         small
% 2.70/0.99  --sat_out_clauses                       false
% 2.70/0.99  
% 2.70/0.99  ------ QBF Options
% 2.70/0.99  
% 2.70/0.99  --qbf_mode                              false
% 2.70/0.99  --qbf_elim_univ                         false
% 2.70/0.99  --qbf_dom_inst                          none
% 2.70/0.99  --qbf_dom_pre_inst                      false
% 2.70/0.99  --qbf_sk_in                             false
% 2.70/0.99  --qbf_pred_elim                         true
% 2.70/0.99  --qbf_split                             512
% 2.70/0.99  
% 2.70/0.99  ------ BMC1 Options
% 2.70/0.99  
% 2.70/0.99  --bmc1_incremental                      false
% 2.70/0.99  --bmc1_axioms                           reachable_all
% 2.70/0.99  --bmc1_min_bound                        0
% 2.70/0.99  --bmc1_max_bound                        -1
% 2.70/0.99  --bmc1_max_bound_default                -1
% 2.70/0.99  --bmc1_symbol_reachability              true
% 2.70/0.99  --bmc1_property_lemmas                  false
% 2.70/0.99  --bmc1_k_induction                      false
% 2.70/0.99  --bmc1_non_equiv_states                 false
% 2.70/0.99  --bmc1_deadlock                         false
% 2.70/0.99  --bmc1_ucm                              false
% 2.70/0.99  --bmc1_add_unsat_core                   none
% 2.70/0.99  --bmc1_unsat_core_children              false
% 2.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.99  --bmc1_out_stat                         full
% 2.70/0.99  --bmc1_ground_init                      false
% 2.70/0.99  --bmc1_pre_inst_next_state              false
% 2.70/0.99  --bmc1_pre_inst_state                   false
% 2.70/0.99  --bmc1_pre_inst_reach_state             false
% 2.70/0.99  --bmc1_out_unsat_core                   false
% 2.70/0.99  --bmc1_aig_witness_out                  false
% 2.70/0.99  --bmc1_verbose                          false
% 2.70/0.99  --bmc1_dump_clauses_tptp                false
% 2.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.99  --bmc1_dump_file                        -
% 2.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.99  --bmc1_ucm_extend_mode                  1
% 2.70/0.99  --bmc1_ucm_init_mode                    2
% 2.70/0.99  --bmc1_ucm_cone_mode                    none
% 2.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.99  --bmc1_ucm_relax_model                  4
% 2.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.99  --bmc1_ucm_layered_model                none
% 2.70/0.99  --bmc1_ucm_max_lemma_size               10
% 2.70/0.99  
% 2.70/0.99  ------ AIG Options
% 2.70/0.99  
% 2.70/0.99  --aig_mode                              false
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation Options
% 2.70/0.99  
% 2.70/0.99  --instantiation_flag                    true
% 2.70/0.99  --inst_sos_flag                         false
% 2.70/0.99  --inst_sos_phase                        true
% 2.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel_side                     none
% 2.70/0.99  --inst_solver_per_active                1400
% 2.70/0.99  --inst_solver_calls_frac                1.
% 2.70/0.99  --inst_passive_queue_type               priority_queues
% 2.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.99  --inst_passive_queues_freq              [25;2]
% 2.70/0.99  --inst_dismatching                      true
% 2.70/0.99  --inst_eager_unprocessed_to_passive     true
% 2.70/0.99  --inst_prop_sim_given                   true
% 2.70/0.99  --inst_prop_sim_new                     false
% 2.70/0.99  --inst_subs_new                         false
% 2.70/0.99  --inst_eq_res_simp                      false
% 2.70/0.99  --inst_subs_given                       false
% 2.70/0.99  --inst_orphan_elimination               true
% 2.70/0.99  --inst_learning_loop_flag               true
% 2.70/0.99  --inst_learning_start                   3000
% 2.70/0.99  --inst_learning_factor                  2
% 2.70/0.99  --inst_start_prop_sim_after_learn       3
% 2.70/0.99  --inst_sel_renew                        solver
% 2.70/0.99  --inst_lit_activity_flag                true
% 2.70/0.99  --inst_restr_to_given                   false
% 2.70/0.99  --inst_activity_threshold               500
% 2.70/0.99  --inst_out_proof                        true
% 2.70/0.99  
% 2.70/0.99  ------ Resolution Options
% 2.70/0.99  
% 2.70/0.99  --resolution_flag                       false
% 2.70/0.99  --res_lit_sel                           adaptive
% 2.70/0.99  --res_lit_sel_side                      none
% 2.70/0.99  --res_ordering                          kbo
% 2.70/0.99  --res_to_prop_solver                    active
% 2.70/0.99  --res_prop_simpl_new                    false
% 2.70/0.99  --res_prop_simpl_given                  true
% 2.70/0.99  --res_passive_queue_type                priority_queues
% 2.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.99  --res_passive_queues_freq               [15;5]
% 2.70/0.99  --res_forward_subs                      full
% 2.70/0.99  --res_backward_subs                     full
% 2.70/0.99  --res_forward_subs_resolution           true
% 2.70/0.99  --res_backward_subs_resolution          true
% 2.70/0.99  --res_orphan_elimination                true
% 2.70/0.99  --res_time_limit                        2.
% 2.70/0.99  --res_out_proof                         true
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Options
% 2.70/0.99  
% 2.70/0.99  --superposition_flag                    true
% 2.70/0.99  --sup_passive_queue_type                priority_queues
% 2.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.99  --demod_completeness_check              fast
% 2.70/0.99  --demod_use_ground                      true
% 2.70/0.99  --sup_to_prop_solver                    passive
% 2.70/0.99  --sup_prop_simpl_new                    true
% 2.70/0.99  --sup_prop_simpl_given                  true
% 2.70/0.99  --sup_fun_splitting                     false
% 2.70/0.99  --sup_smt_interval                      50000
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Simplification Setup
% 2.70/0.99  
% 2.70/0.99  --sup_indices_passive                   []
% 2.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_full_bw                           [BwDemod]
% 2.70/0.99  --sup_immed_triv                        [TrivRules]
% 2.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_immed_bw_main                     []
% 2.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.99  
% 2.70/0.99  ------ Combination Options
% 2.70/0.99  
% 2.70/0.99  --comb_res_mult                         3
% 2.70/0.99  --comb_sup_mult                         2
% 2.70/0.99  --comb_inst_mult                        10
% 2.70/0.99  
% 2.70/0.99  ------ Debug Options
% 2.70/0.99  
% 2.70/0.99  --dbg_backtrace                         false
% 2.70/0.99  --dbg_dump_prop_clauses                 false
% 2.70/0.99  --dbg_dump_prop_clauses_file            -
% 2.70/0.99  --dbg_out_stat                          false
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  ------ Proving...
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  % SZS output start Saturation for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  fof(f3,axiom,(
% 2.70/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f52,plain,(
% 2.70/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.70/0.99    inference(nnf_transformation,[],[f3])).
% 2.70/0.99  
% 2.70/0.99  fof(f53,plain,(
% 2.70/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.70/0.99    inference(rectify,[],[f52])).
% 2.70/0.99  
% 2.70/0.99  fof(f54,plain,(
% 2.70/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f55,plain,(
% 2.70/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).
% 2.70/0.99  
% 2.70/0.99  fof(f72,plain,(
% 2.70/0.99    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f55])).
% 2.70/0.99  
% 2.70/0.99  fof(f70,plain,(
% 2.70/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.70/0.99    inference(cnf_transformation,[],[f55])).
% 2.70/0.99  
% 2.70/0.99  fof(f110,plain,(
% 2.70/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.70/0.99    inference(equality_resolution,[],[f70])).
% 2.70/0.99  
% 2.70/0.99  fof(f7,axiom,(
% 2.70/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f56,plain,(
% 2.70/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.70/0.99    inference(nnf_transformation,[],[f7])).
% 2.70/0.99  
% 2.70/0.99  fof(f78,plain,(
% 2.70/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f56])).
% 2.70/0.99  
% 2.70/0.99  fof(f11,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f35,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(ennf_transformation,[],[f11])).
% 2.70/0.99  
% 2.70/0.99  fof(f81,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f35])).
% 2.70/0.99  
% 2.70/0.99  fof(f71,plain,(
% 2.70/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.70/0.99    inference(cnf_transformation,[],[f55])).
% 2.70/0.99  
% 2.70/0.99  fof(f109,plain,(
% 2.70/0.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.70/0.99    inference(equality_resolution,[],[f71])).
% 2.70/0.99  
% 2.70/0.99  fof(f4,axiom,(
% 2.70/0.99    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f74,plain,(
% 2.70/0.99    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 2.70/0.99    inference(cnf_transformation,[],[f4])).
% 2.70/0.99  
% 2.70/0.99  fof(f18,axiom,(
% 2.70/0.99    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f24,plain,(
% 2.70/0.99    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 2.70/0.99    inference(rectify,[],[f18])).
% 2.70/0.99  
% 2.70/0.99  fof(f45,plain,(
% 2.70/0.99    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 2.70/0.99    inference(ennf_transformation,[],[f24])).
% 2.70/0.99  
% 2.70/0.99  fof(f58,plain,(
% 2.70/0.99    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK1(X0),X0) & k1_xboole_0 != sK1(X0)))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f59,plain,(
% 2.70/0.99    ! [X0] : (((r2_hidden(sK1(X0),X0) & k1_xboole_0 != sK1(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f58])).
% 2.70/0.99  
% 2.70/0.99  fof(f91,plain,(
% 2.70/0.99    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 2.70/0.99    inference(cnf_transformation,[],[f59])).
% 2.70/0.99  
% 2.70/0.99  fof(f73,plain,(
% 2.70/0.99    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | ~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f55])).
% 2.70/0.99  
% 2.70/0.99  fof(f22,conjecture,(
% 2.70/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f23,negated_conjecture,(
% 2.70/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v23_waybel_0(X2,X0,X1) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2)))))))),
% 2.70/0.99    inference(negated_conjecture,[],[f22])).
% 2.70/0.99  
% 2.70/0.99  fof(f25,plain,(
% 2.70/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k2_relat_1(k2_funct_1(X2)) = u1_struct_0(X0) & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_funct_1(X2))))))),
% 2.70/0.99    inference(pure_predicate_removal,[],[f23])).
% 2.70/0.99  
% 2.70/0.99  fof(f50,plain,(
% 2.70/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_orders_2(X1) & ~v2_struct_0(X1))) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.70/0.99    inference(ennf_transformation,[],[f25])).
% 2.70/0.99  
% 2.70/0.99  fof(f51,plain,(
% 2.70/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 2.70/0.99    inference(flattening,[],[f50])).
% 2.70/0.99  
% 2.70/0.99  fof(f66,plain,(
% 2.70/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(sK5),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(sK5))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f65,plain,(
% 2.70/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(sK4),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_orders_2(sK4) & ~v2_struct_0(sK4))) )),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f64,plain,(
% 2.70/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(X0) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relat_1(k2_funct_1(X2)) != u1_struct_0(sK3) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(k2_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f67,plain,(
% 2.70/0.99    (((k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3) | ~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_funct_1(sK5),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_funct_1(sK5))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & l1_orders_2(sK4) & ~v2_struct_0(sK4)) & l1_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f51,f66,f65,f64])).
% 2.70/0.99  
% 2.70/0.99  fof(f105,plain,(
% 2.70/0.99    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 2.70/0.99    inference(cnf_transformation,[],[f67])).
% 2.70/0.99  
% 2.70/0.99  fof(f13,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f38,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.70/0.99    inference(ennf_transformation,[],[f13])).
% 2.70/0.99  
% 2.70/0.99  fof(f39,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.70/0.99    inference(flattening,[],[f38])).
% 2.70/0.99  
% 2.70/0.99  fof(f84,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f39])).
% 2.70/0.99  
% 2.70/0.99  fof(f10,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f28,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.70/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.70/0.99  
% 2.70/0.99  fof(f34,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(ennf_transformation,[],[f28])).
% 2.70/0.99  
% 2.70/0.99  fof(f80,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f34])).
% 2.70/0.99  
% 2.70/0.99  fof(f12,axiom,(
% 2.70/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f36,plain,(
% 2.70/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.70/0.99    inference(ennf_transformation,[],[f12])).
% 2.70/0.99  
% 2.70/0.99  fof(f37,plain,(
% 2.70/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.70/0.99    inference(flattening,[],[f36])).
% 2.70/0.99  
% 2.70/0.99  fof(f57,plain,(
% 2.70/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.70/0.99    inference(nnf_transformation,[],[f37])).
% 2.70/0.99  
% 2.70/0.99  fof(f82,plain,(
% 2.70/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f57])).
% 2.70/0.99  
% 2.70/0.99  fof(f9,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f33,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.99    inference(ennf_transformation,[],[f9])).
% 2.70/0.99  
% 2.70/0.99  fof(f79,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f33])).
% 2.70/0.99  
% 2.70/0.99  fof(f104,plain,(
% 2.70/0.99    v1_funct_1(sK5)),
% 2.70/0.99    inference(cnf_transformation,[],[f67])).
% 2.70/0.99  
% 2.70/0.99  fof(f106,plain,(
% 2.70/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 2.70/0.99    inference(cnf_transformation,[],[f67])).
% 2.70/0.99  
% 2.70/0.99  fof(f19,axiom,(
% 2.70/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f46,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 2.70/0.99    inference(ennf_transformation,[],[f19])).
% 2.70/0.99  
% 2.70/0.99  fof(f60,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 2.70/0.99    inference(nnf_transformation,[],[f46])).
% 2.70/0.99  
% 2.70/0.99  fof(f61,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 2.70/0.99    inference(flattening,[],[f60])).
% 2.70/0.99  
% 2.70/0.99  fof(f94,plain,(
% 2.70/0.99    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f61])).
% 2.70/0.99  
% 2.70/0.99  fof(f20,axiom,(
% 2.70/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => l1_orders_2(X1)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f47,plain,(
% 2.70/0.99    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 2.70/0.99    inference(ennf_transformation,[],[f20])).
% 2.70/0.99  
% 2.70/0.99  fof(f97,plain,(
% 2.70/0.99    ( ! [X0,X1] : (l1_orders_2(X1) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f47])).
% 2.70/0.99  
% 2.70/0.99  fof(f21,axiom,(
% 2.70/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_yellow_0(X1,X0) & v1_orders_2(X1) & ~v2_struct_0(X1) & m1_yellow_0(X1,X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f26,plain,(
% 2.70/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ? [X1] : (v1_orders_2(X1) & ~v2_struct_0(X1) & m1_yellow_0(X1,X0)))),
% 2.70/0.99    inference(pure_predicate_removal,[],[f21])).
% 2.70/0.99  
% 2.70/0.99  fof(f27,plain,(
% 2.70/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v2_struct_0(X1) & m1_yellow_0(X1,X0)))),
% 2.70/0.99    inference(pure_predicate_removal,[],[f26])).
% 2.70/0.99  
% 2.70/0.99  fof(f48,plain,(
% 2.70/0.99    ! [X0] : (? [X1] : (~v2_struct_0(X1) & m1_yellow_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.70/0.99    inference(ennf_transformation,[],[f27])).
% 2.70/0.99  
% 2.70/0.99  fof(f49,plain,(
% 2.70/0.99    ! [X0] : (? [X1] : (~v2_struct_0(X1) & m1_yellow_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.70/0.99    inference(flattening,[],[f48])).
% 2.70/0.99  
% 2.70/0.99  fof(f62,plain,(
% 2.70/0.99    ! [X0] : (? [X1] : (~v2_struct_0(X1) & m1_yellow_0(X1,X0)) => (~v2_struct_0(sK2(X0)) & m1_yellow_0(sK2(X0),X0)))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f63,plain,(
% 2.70/0.99    ! [X0] : ((~v2_struct_0(sK2(X0)) & m1_yellow_0(sK2(X0),X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f62])).
% 2.70/0.99  
% 2.70/0.99  fof(f98,plain,(
% 2.70/0.99    ( ! [X0] : (m1_yellow_0(sK2(X0),X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f63])).
% 2.70/0.99  
% 2.70/0.99  fof(f102,plain,(
% 2.70/0.99    ~v2_struct_0(sK4)),
% 2.70/0.99    inference(cnf_transformation,[],[f67])).
% 2.70/0.99  
% 2.70/0.99  fof(f103,plain,(
% 2.70/0.99    l1_orders_2(sK4)),
% 2.70/0.99    inference(cnf_transformation,[],[f67])).
% 2.70/0.99  
% 2.70/0.99  fof(f99,plain,(
% 2.70/0.99    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f63])).
% 2.70/0.99  
% 2.70/0.99  fof(f17,axiom,(
% 2.70/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f44,plain,(
% 2.70/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.70/0.99    inference(ennf_transformation,[],[f17])).
% 2.70/0.99  
% 2.70/0.99  fof(f90,plain,(
% 2.70/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f44])).
% 2.70/0.99  
% 2.70/0.99  fof(f1,axiom,(
% 2.70/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f68,plain,(
% 2.70/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f1])).
% 2.70/0.99  
% 2.70/0.99  fof(f2,axiom,(
% 2.70/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f31,plain,(
% 2.70/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.70/0.99    inference(ennf_transformation,[],[f2])).
% 2.70/0.99  
% 2.70/0.99  fof(f32,plain,(
% 2.70/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.70/0.99    inference(flattening,[],[f31])).
% 2.70/0.99  
% 2.70/0.99  fof(f69,plain,(
% 2.70/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f32])).
% 2.70/0.99  
% 2.70/0.99  fof(f16,axiom,(
% 2.70/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f42,plain,(
% 2.70/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.70/0.99    inference(ennf_transformation,[],[f16])).
% 2.70/0.99  
% 2.70/0.99  fof(f43,plain,(
% 2.70/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.70/0.99    inference(flattening,[],[f42])).
% 2.70/0.99  
% 2.70/0.99  fof(f89,plain,(
% 2.70/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f43])).
% 2.70/0.99  
% 2.70/0.99  fof(f100,plain,(
% 2.70/0.99    ~v2_struct_0(sK3)),
% 2.70/0.99    inference(cnf_transformation,[],[f67])).
% 2.70/0.99  
% 2.70/0.99  fof(f101,plain,(
% 2.70/0.99    l1_orders_2(sK3)),
% 2.70/0.99    inference(cnf_transformation,[],[f67])).
% 2.70/0.99  
% 2.70/0.99  fof(f93,plain,(
% 2.70/0.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = k3_tarski(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f59])).
% 2.70/0.99  
% 2.70/0.99  fof(f15,axiom,(
% 2.70/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f40,plain,(
% 2.70/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.70/0.99    inference(ennf_transformation,[],[f15])).
% 2.70/0.99  
% 2.70/0.99  fof(f41,plain,(
% 2.70/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.70/0.99    inference(flattening,[],[f40])).
% 2.70/0.99  
% 2.70/0.99  fof(f88,plain,(
% 2.70/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f41])).
% 2.70/0.99  
% 2.70/0.99  fof(f6,axiom,(
% 2.70/0.99    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f76,plain,(
% 2.70/0.99    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f6])).
% 2.70/0.99  
% 2.70/0.99  fof(f5,axiom,(
% 2.70/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 2.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f75,plain,(
% 2.70/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f5])).
% 2.70/0.99  
% 2.70/0.99  fof(f108,plain,(
% 2.70/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.70/0.99    inference(definition_unfolding,[],[f76,f75])).
% 2.70/0.99  
% 2.70/0.99  fof(f107,plain,(
% 2.70/0.99    k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3) | ~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_funct_1(sK5),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_funct_1(sK5))),
% 2.70/0.99    inference(cnf_transformation,[],[f67])).
% 2.70/0.99  
% 2.70/0.99  fof(f85,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f39])).
% 2.70/0.99  
% 2.70/0.99  fof(f112,plain,(
% 2.70/0.99    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 2.70/0.99    inference(equality_resolution,[],[f85])).
% 2.70/0.99  
% 2.70/0.99  fof(f77,plain,(
% 2.70/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f56])).
% 2.70/0.99  
% 2.70/0.99  fof(f87,plain,(
% 2.70/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f41])).
% 2.70/0.99  
% 2.70/0.99  fof(f95,plain,(
% 2.70/0.99    ( ! [X0,X1] : (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f61])).
% 2.70/0.99  
% 2.70/0.99  fof(f92,plain,(
% 2.70/0.99    ( ! [X0] : (k1_xboole_0 != sK1(X0) | k1_xboole_0 = k3_tarski(X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f59])).
% 2.70/0.99  
% 2.70/0.99  cnf(c_465,plain,
% 2.70/0.99      ( ~ m1_yellow_0(X0,X1) | m1_yellow_0(X2,X1) | X2 != X0 ),
% 2.70/0.99      theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_461,plain,
% 2.70/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 2.70/0.99      theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_460,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/0.99      | v1_funct_2(X3,X4,X5)
% 2.70/0.99      | X3 != X0
% 2.70/0.99      | X4 != X1
% 2.70/0.99      | X5 != X2 ),
% 2.70/0.99      theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_459,plain,
% 2.70/0.99      ( ~ v1_partfun1(X0,X1) | v1_partfun1(X0,X2) | X2 != X1 ),
% 2.70/0.99      theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_457,plain,
% 2.70/0.99      ( ~ v4_relat_1(X0,X1) | v4_relat_1(X0,X2) | X2 != X1 ),
% 2.70/0.99      theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_451,plain,
% 2.70/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.70/0.99      theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_449,plain,
% 2.70/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,X2) | X2 != X1 ),
% 2.70/0.99      theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2064,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3,plain,
% 2.70/0.99      ( r2_hidden(sK0(X0,X1),X1)
% 2.70/0.99      | r1_tarski(sK0(X0,X1),X0)
% 2.70/0.99      | k1_zfmisc_1(X0) = X1 ),
% 2.70/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2743,plain,
% 2.70/0.99      ( k1_zfmisc_1(X0) = X1
% 2.70/0.99      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.70/0.99      | r1_tarski(sK0(X0,X1),X0) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5,plain,
% 2.70/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f110]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2741,plain,
% 2.70/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.70/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4761,plain,
% 2.70/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.70/0.99      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) = iProver_top
% 2.70/0.99      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2743,c_2741]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_8,plain,
% 2.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2739,plain,
% 2.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.70/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_12,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2737,plain,
% 2.70/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4212,plain,
% 2.70/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.70/0.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2739,c_2737]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5328,plain,
% 2.70/0.99      ( k2_relset_1(X0,X1,sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2))) = k2_relat_1(sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2)))
% 2.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)
% 2.70/0.99      | r1_tarski(sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(X2)),X2) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_4761,c_4212]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5661,plain,
% 2.70/0.99      ( k2_relset_1(X0,X1,sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
% 2.70/0.99      | k2_relset_1(X2,X3,sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) = k2_relat_1(sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))
% 2.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_5328,c_4212]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5323,plain,
% 2.70/0.99      ( k2_relset_1(X0,X1,sK0(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK0(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
% 2.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(X2)
% 2.70/0.99      | r1_tarski(sK0(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_4761,c_4212]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5586,plain,
% 2.70/0.99      ( k2_relset_1(X0,X1,sK0(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK0(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
% 2.70/0.99      | k2_relset_1(X2,X3,sK0(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK0(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
% 2.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_5323,c_4212]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4,plain,
% 2.70/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f109]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2742,plain,
% 2.70/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.70/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_6,plain,
% 2.70/0.99      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 2.70/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_24,plain,
% 2.70/0.99      ( ~ r2_hidden(X0,X1) | k3_tarski(X1) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.70/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2735,plain,
% 2.70/0.99      ( k3_tarski(X0) != k1_xboole_0
% 2.70/0.99      | k1_xboole_0 = X1
% 2.70/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4150,plain,
% 2.70/0.99      ( k1_xboole_0 != X0
% 2.70/0.99      | k1_xboole_0 = X1
% 2.70/0.99      | r2_hidden(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_6,c_2735]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4156,plain,
% 2.70/0.99      ( k1_xboole_0 = X0
% 2.70/0.99      | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.70/0.99      inference(equality_resolution,[status(thm)],[c_4150]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4555,plain,
% 2.70/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2742,c_4156]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4760,plain,
% 2.70/0.99      ( sK0(k1_xboole_0,X0) = k1_xboole_0
% 2.70/0.99      | k1_zfmisc_1(k1_xboole_0) = X0
% 2.70/0.99      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2743,c_4555]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4876,plain,
% 2.70/0.99      ( sK0(k1_xboole_0,k1_zfmisc_1(X0)) = k1_xboole_0
% 2.70/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 2.70/0.99      | r1_tarski(sK0(k1_xboole_0,k1_zfmisc_1(X0)),X0) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_4760,c_2741]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5170,plain,
% 2.70/0.99      ( k2_relset_1(X0,X1,sK0(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK0(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
% 2.70/0.99      | sK0(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = k1_xboole_0
% 2.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0) ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_4876,c_4212]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4762,plain,
% 2.70/0.99      ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
% 2.70/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 2.70/0.99      | r1_tarski(sK0(X0,k1_zfmisc_1(k1_xboole_0)),X0) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2743,c_4156]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2,plain,
% 2.70/0.99      ( ~ r2_hidden(sK0(X0,X1),X1)
% 2.70/0.99      | ~ r1_tarski(sK0(X0,X1),X0)
% 2.70/0.99      | k1_zfmisc_1(X0) = X1 ),
% 2.70/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2744,plain,
% 2.70/0.99      ( k1_zfmisc_1(X0) = X1
% 2.70/0.99      | r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.70/0.99      | r1_tarski(sK0(X0,X1),X0) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4791,plain,
% 2.70/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.70/0.99      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) != iProver_top
% 2.70/0.99      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2742,c_2744]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5031,plain,
% 2.70/0.99      ( sK0(X0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
% 2.70/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
% 2.70/0.99      | r1_tarski(sK0(X0,k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_4762,c_4791]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5030,plain,
% 2.70/0.99      ( k2_relset_1(X0,X1,sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0))) = k2_relat_1(sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)))
% 2.70/0.99      | sK0(k2_zfmisc_1(X0,X1),k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
% 2.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k1_xboole_0) ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_4762,c_4212]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_33,negated_conjecture,
% 2.70/0.99      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f105]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_16,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/0.99      | v1_partfun1(X0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | k1_xboole_0 = X2 ),
% 2.70/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_11,plain,
% 2.70/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_14,plain,
% 2.70/0.99      ( ~ v1_partfun1(X0,X1)
% 2.70/0.99      | ~ v4_relat_1(X0,X1)
% 2.70/0.99      | ~ v1_relat_1(X0)
% 2.70/0.99      | k1_relat_1(X0) = X1 ),
% 2.70/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_555,plain,
% 2.70/0.99      ( ~ v1_partfun1(X0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ v1_relat_1(X0)
% 2.70/0.99      | k1_relat_1(X0) = X1 ),
% 2.70/0.99      inference(resolution,[status(thm)],[c_11,c_14]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_10,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_559,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ v1_partfun1(X0,X1)
% 2.70/0.99      | k1_relat_1(X0) = X1 ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_555,c_14,c_11,c_10]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_560,plain,
% 2.70/0.99      ( ~ v1_partfun1(X0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | k1_relat_1(X0) = X1 ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_559]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_633,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | k1_relat_1(X0) = X1
% 2.70/0.99      | k1_xboole_0 = X2 ),
% 2.70/0.99      inference(resolution,[status(thm)],[c_16,c_560]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_637,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ v1_funct_2(X0,X1,X2)
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | k1_relat_1(X0) = X1
% 2.70/0.99      | k1_xboole_0 = X2 ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_633,c_16,c_560]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_638,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | k1_relat_1(X0) = X1
% 2.70/0.99      | k1_xboole_0 = X2 ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_637]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_34,negated_conjecture,
% 2.70/0.99      ( v1_funct_1(sK5) ),
% 2.70/0.99      inference(cnf_transformation,[],[f104]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_710,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | k1_relat_1(X0) = X1
% 2.70/0.99      | sK5 != X0
% 2.70/0.99      | k1_xboole_0 = X2 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_638,c_34]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_711,plain,
% 2.70/0.99      ( ~ v1_funct_2(sK5,X0,X1)
% 2.70/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.70/0.99      | k1_relat_1(sK5) = X0
% 2.70/0.99      | k1_xboole_0 = X1 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_710]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_868,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.70/0.99      | u1_struct_0(sK4) != X1
% 2.70/0.99      | u1_struct_0(sK3) != X0
% 2.70/0.99      | k1_relat_1(sK5) = X0
% 2.70/0.99      | sK5 != sK5
% 2.70/0.99      | k1_xboole_0 = X1 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_711]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_869,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 2.70/0.99      | k1_relat_1(sK5) = u1_struct_0(sK3)
% 2.70/0.99      | k1_xboole_0 = u1_struct_0(sK4) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_868]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_32,negated_conjecture,
% 2.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f106]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_871,plain,
% 2.70/0.99      ( k1_relat_1(sK5) = u1_struct_0(sK3) | k1_xboole_0 = u1_struct_0(sK4) ),
% 2.70/0.99      inference(global_propositional_subsumption,[status(thm)],[c_869,c_32]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_27,plain,
% 2.70/0.99      ( ~ m1_yellow_0(X0,X1)
% 2.70/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.70/0.99      | ~ l1_orders_2(X1)
% 2.70/0.99      | ~ l1_orders_2(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_28,plain,
% 2.70/0.99      ( ~ m1_yellow_0(X0,X1) | ~ l1_orders_2(X1) | l1_orders_2(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_218,plain,
% 2.70/0.99      ( ~ l1_orders_2(X1)
% 2.70/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.70/0.99      | ~ m1_yellow_0(X0,X1) ),
% 2.70/0.99      inference(global_propositional_subsumption,[status(thm)],[c_27,c_28]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_219,plain,
% 2.70/0.99      ( ~ m1_yellow_0(X0,X1)
% 2.70/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.70/0.99      | ~ l1_orders_2(X1) ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_218]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_30,plain,
% 2.70/0.99      ( m1_yellow_0(sK2(X0),X0) | ~ l1_orders_2(X0) | v2_struct_0(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1034,plain,
% 2.70/0.99      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.70/0.99      | ~ l1_orders_2(X1)
% 2.70/0.99      | ~ l1_orders_2(X2)
% 2.70/0.99      | v2_struct_0(X2)
% 2.70/0.99      | X2 != X1
% 2.70/0.99      | sK2(X2) != X0 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_219,c_30]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1035,plain,
% 2.70/0.99      ( r1_tarski(u1_struct_0(sK2(X0)),u1_struct_0(X0))
% 2.70/0.99      | ~ l1_orders_2(X0)
% 2.70/0.99      | v2_struct_0(X0) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_1034]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2720,plain,
% 2.70/0.99      ( r1_tarski(u1_struct_0(sK2(X0)),u1_struct_0(X0)) = iProver_top
% 2.70/0.99      | l1_orders_2(X0) != iProver_top
% 2.70/0.99      | v2_struct_0(X0) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1035]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3661,plain,
% 2.70/0.99      ( u1_struct_0(sK3) = k1_relat_1(sK5)
% 2.70/0.99      | r1_tarski(u1_struct_0(sK2(sK4)),k1_xboole_0) = iProver_top
% 2.70/0.99      | l1_orders_2(sK4) != iProver_top
% 2.70/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_871,c_2720]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_36,negated_conjecture,
% 2.70/0.99      ( ~ v2_struct_0(sK4) ),
% 2.70/0.99      inference(cnf_transformation,[],[f102]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_41,plain,
% 2.70/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_35,negated_conjecture,
% 2.70/0.99      ( l1_orders_2(sK4) ),
% 2.70/0.99      inference(cnf_transformation,[],[f103]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_42,plain,
% 2.70/0.99      ( l1_orders_2(sK4) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_29,plain,
% 2.70/0.99      ( ~ l1_orders_2(X0) | v2_struct_0(X0) | ~ v2_struct_0(sK2(X0)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2943,plain,
% 2.70/0.99      ( ~ l1_orders_2(sK4) | ~ v2_struct_0(sK2(sK4)) | v2_struct_0(sK4) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2944,plain,
% 2.70/0.99      ( l1_orders_2(sK4) != iProver_top
% 2.70/0.99      | v2_struct_0(sK2(sK4)) != iProver_top
% 2.70/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2943]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1049,plain,
% 2.70/0.99      ( ~ l1_orders_2(X0)
% 2.70/0.99      | ~ l1_orders_2(X1)
% 2.70/0.99      | l1_orders_2(X2)
% 2.70/0.99      | v2_struct_0(X1)
% 2.70/0.99      | X1 != X0
% 2.70/0.99      | sK2(X1) != X2 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1050,plain,
% 2.70/0.99      ( ~ l1_orders_2(X0) | l1_orders_2(sK2(X0)) | v2_struct_0(X0) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_1049]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2955,plain,
% 2.70/0.99      ( l1_orders_2(sK2(sK4)) | ~ l1_orders_2(sK4) | v2_struct_0(sK4) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1050]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2956,plain,
% 2.70/0.99      ( l1_orders_2(sK2(sK4)) = iProver_top
% 2.70/0.99      | l1_orders_2(sK4) != iProver_top
% 2.70/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2955]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_21,plain,
% 2.70/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_0,plain,
% 2.70/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_503,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X0) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_504,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_503]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_20,plain,
% 2.70/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_518,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,k1_xboole_0)
% 2.70/0.99      | v2_struct_0(X1)
% 2.70/0.99      | ~ l1_struct_0(X1)
% 2.70/0.99      | u1_struct_0(X1) != X0 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_504,c_20]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_519,plain,
% 2.70/0.99      ( ~ r1_tarski(u1_struct_0(X0),k1_xboole_0)
% 2.70/0.99      | v2_struct_0(X0)
% 2.70/0.99      | ~ l1_struct_0(X0) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_518]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_537,plain,
% 2.70/0.99      ( ~ r1_tarski(u1_struct_0(X0),k1_xboole_0)
% 2.70/0.99      | ~ l1_orders_2(X0)
% 2.70/0.99      | v2_struct_0(X0) ),
% 2.70/0.99      inference(resolution,[status(thm)],[c_21,c_519]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3070,plain,
% 2.70/0.99      ( ~ r1_tarski(u1_struct_0(sK2(sK4)),k1_xboole_0)
% 2.70/0.99      | ~ l1_orders_2(sK2(sK4))
% 2.70/0.99      | v2_struct_0(sK2(sK4)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_537]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3074,plain,
% 2.70/0.99      ( r1_tarski(u1_struct_0(sK2(sK4)),k1_xboole_0) != iProver_top
% 2.70/0.99      | l1_orders_2(sK2(sK4)) != iProver_top
% 2.70/0.99      | v2_struct_0(sK2(sK4)) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_3070]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3842,plain,
% 2.70/0.99      ( u1_struct_0(sK3) = k1_relat_1(sK5) ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_3661,c_41,c_42,c_2944,c_2956,c_3074]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2728,plain,
% 2.70/0.99      ( r1_tarski(u1_struct_0(X0),k1_xboole_0) != iProver_top
% 2.70/0.99      | l1_orders_2(X0) != iProver_top
% 2.70/0.99      | v2_struct_0(X0) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4677,plain,
% 2.70/0.99      ( r1_tarski(k1_relat_1(sK5),k1_xboole_0) != iProver_top
% 2.70/0.99      | l1_orders_2(sK3) != iProver_top
% 2.70/0.99      | v2_struct_0(sK3) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_3842,c_2728]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_38,negated_conjecture,
% 2.70/0.99      ( ~ v2_struct_0(sK3) ),
% 2.70/0.99      inference(cnf_transformation,[],[f100]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_39,plain,
% 2.70/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_37,negated_conjecture,
% 2.70/0.99      ( l1_orders_2(sK3) ),
% 2.70/0.99      inference(cnf_transformation,[],[f101]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_40,plain,
% 2.70/0.99      ( l1_orders_2(sK3) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4948,plain,
% 2.70/0.99      ( r1_tarski(k1_relat_1(sK5),k1_xboole_0) != iProver_top ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_4677,c_39,c_40]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4875,plain,
% 2.70/0.99      ( sK0(k1_xboole_0,X0) = k1_xboole_0
% 2.70/0.99      | k1_zfmisc_1(k1_xboole_0) = X0
% 2.70/0.99      | r1_tarski(sK0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_4760,c_2744]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_22,plain,
% 2.70/0.99      ( r2_hidden(sK1(X0),X0) | k3_tarski(X0) = k1_xboole_0 ),
% 2.70/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2736,plain,
% 2.70/0.99      ( k3_tarski(X0) = k1_xboole_0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3735,plain,
% 2.70/0.99      ( k3_tarski(k1_zfmisc_1(X0)) = k1_xboole_0
% 2.70/0.99      | r1_tarski(sK1(k1_zfmisc_1(X0)),X0) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2736,c_2741]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3736,plain,
% 2.70/0.99      ( k1_xboole_0 = X0 | r1_tarski(sK1(k1_zfmisc_1(X0)),X0) = iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_3735,c_6]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4854,plain,
% 2.70/0.99      ( k2_relset_1(X0,X1,sK1(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k2_relat_1(sK1(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
% 2.70/0.99      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_3736,c_4212]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4852,plain,
% 2.70/0.99      ( k2_relset_1(X0,X1,sK0(k2_zfmisc_1(X0,X1),X2)) = k2_relat_1(sK0(k2_zfmisc_1(X0,X1),X2))
% 2.70/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = X2
% 2.70/0.99      | r2_hidden(sK0(k2_zfmisc_1(X0,X1),X2),X2) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2743,c_4212]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2733,plain,
% 2.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3849,plain,
% 2.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK4)))) = iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_3842,c_2733]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4214,plain,
% 2.70/0.99      ( k2_relset_1(k1_relat_1(sK5),u1_struct_0(sK4),sK5) = k2_relat_1(sK5) ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_3849,c_2737]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_17,plain,
% 2.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | ~ v1_relat_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_736,plain,
% 2.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.70/0.99      | ~ v1_relat_1(X0)
% 2.70/0.99      | sK5 != X0 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_737,plain,
% 2.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5))))
% 2.70/0.99      | ~ v1_relat_1(sK5) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_736]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_782,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5))))
% 2.70/0.99      | sK5 != X0 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_737]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_783,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.70/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_782]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2727,plain,
% 2.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.70/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_45,plain,
% 2.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2940,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 2.70/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_783]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2941,plain,
% 2.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 2.70/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2940]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3445,plain,
% 2.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) = iProver_top ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_2727,c_45,c_2941]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4213,plain,
% 2.70/0.99      ( k2_relset_1(k1_relat_1(sK5),k2_relat_1(sK5),sK5) = k2_relat_1(sK5) ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_3445,c_2737]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_7,plain,
% 2.70/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f108]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2740,plain,
% 2.70/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4211,plain,
% 2.70/0.99      ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2740,c_2737]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3867,plain,
% 2.70/0.99      ( r1_tarski(u1_struct_0(sK2(sK3)),k1_relat_1(sK5)) = iProver_top
% 2.70/0.99      | l1_orders_2(sK3) != iProver_top
% 2.70/0.99      | v2_struct_0(sK3) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_3842,c_2720]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4067,plain,
% 2.70/0.99      ( r1_tarski(u1_struct_0(sK2(sK3)),k1_relat_1(sK5)) = iProver_top ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_3867,c_39,c_40]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_31,negated_conjecture,
% 2.70/0.99      ( ~ v1_funct_2(k2_funct_1(sK5),u1_struct_0(sK4),u1_struct_0(sK3))
% 2.70/0.99      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 2.70/0.99      | ~ v1_funct_1(k2_funct_1(sK5))
% 2.70/0.99      | k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3) ),
% 2.70/0.99      inference(cnf_transformation,[],[f107]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_746,plain,
% 2.70/0.99      ( ~ v1_funct_2(k2_funct_1(sK5),u1_struct_0(sK4),u1_struct_0(sK3))
% 2.70/0.99      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 2.70/0.99      | k2_funct_1(sK5) != sK5
% 2.70/0.99      | k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3) ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_34]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_812,plain,
% 2.70/0.99      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 2.70/0.99      | k2_funct_1(sK5) != sK5
% 2.70/0.99      | u1_struct_0(sK4) != u1_struct_0(sK3)
% 2.70/0.99      | k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3) ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_746,c_33]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2726,plain,
% 2.70/0.99      ( k2_funct_1(sK5) != sK5
% 2.70/0.99      | u1_struct_0(sK4) != u1_struct_0(sK3)
% 2.70/0.99      | k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3)
% 2.70/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3848,plain,
% 2.70/0.99      ( k2_funct_1(sK5) != sK5
% 2.70/0.99      | u1_struct_0(sK4) != k1_relat_1(sK5)
% 2.70/0.99      | k2_relat_1(k2_funct_1(sK5)) != k1_relat_1(sK5)
% 2.70/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),k1_relat_1(sK5)))) != iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_3842,c_2726]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_15,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.70/0.99      | v1_partfun1(X0,k1_xboole_0)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.70/0.99      | ~ v1_funct_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f112]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_659,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | X0 != X2
% 2.70/0.99      | k1_relat_1(X2) = X3
% 2.70/0.99      | k1_xboole_0 != X3 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_560,c_15]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_660,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | k1_relat_1(X0) = k1_xboole_0 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_659]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_692,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 2.70/0.99      | k1_relat_1(X0) = k1_xboole_0
% 2.70/0.99      | sK5 != X0 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_660,c_34]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_693,plain,
% 2.70/0.99      ( ~ v1_funct_2(sK5,k1_xboole_0,X0)
% 2.70/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.70/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.70/0.99      | k1_relat_1(sK5) = k1_xboole_0 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_692]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_850,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.70/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.70/0.99      | u1_struct_0(sK4) != X1
% 2.70/0.99      | u1_struct_0(sK3) != k1_xboole_0
% 2.70/0.99      | k1_relat_1(sK5) = k1_xboole_0
% 2.70/0.99      | sK5 != sK5 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_693]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_851,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.70/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK4))))
% 2.70/0.99      | u1_struct_0(sK3) != k1_xboole_0
% 2.70/0.99      | k1_relat_1(sK5) = k1_xboole_0 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_850]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2061,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK4))))
% 2.70/0.99      | sP0_iProver_split
% 2.70/0.99      | u1_struct_0(sK3) != k1_xboole_0
% 2.70/0.99      | k1_relat_1(sK5) = k1_xboole_0 ),
% 2.70/0.99      inference(splitting,
% 2.70/0.99                [splitting(split),new_symbols(definition,[])],
% 2.70/0.99                [c_851]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2722,plain,
% 2.70/0.99      ( u1_struct_0(sK3) != k1_xboole_0
% 2.70/0.99      | k1_relat_1(sK5) = k1_xboole_0
% 2.70/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK4)))) != iProver_top
% 2.70/0.99      | sP0_iProver_split = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2061]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2060,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.70/0.99      | ~ sP0_iProver_split ),
% 2.70/0.99      inference(splitting,
% 2.70/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.70/0.99                [c_851]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2723,plain,
% 2.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 2.70/0.99      | sP0_iProver_split != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2060]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2855,plain,
% 2.70/0.99      ( u1_struct_0(sK3) != k1_xboole_0
% 2.70/0.99      | k1_relat_1(sK5) = k1_xboole_0
% 2.70/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK4)))) != iProver_top ),
% 2.70/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2722,c_2723]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_9,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_105,plain,
% 2.70/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.70/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_111,plain,
% 2.70/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_113,plain,
% 2.70/0.99      ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_297,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.70/0.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_298,plain,
% 2.70/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_297]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_980,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1)
% 2.70/0.99      | X2 != X0
% 2.70/0.99      | k3_tarski(X3) != k1_xboole_0
% 2.70/0.99      | k1_zfmisc_1(X1) != X3
% 2.70/0.99      | k1_xboole_0 = X2 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_298,c_24]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_981,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1)
% 2.70/0.99      | k3_tarski(k1_zfmisc_1(X1)) != k1_xboole_0
% 2.70/0.99      | k1_xboole_0 = X0 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_980]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_983,plain,
% 2.70/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.70/0.99      | k3_tarski(k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
% 2.70/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_981]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2952,plain,
% 2.70/0.99      ( ~ r1_tarski(u1_struct_0(sK3),k1_xboole_0)
% 2.70/0.99      | ~ l1_orders_2(sK3)
% 2.70/0.99      | v2_struct_0(sK3) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_537]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2067,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.70/0.99      theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3056,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1)
% 2.70/0.99      | r1_tarski(u1_struct_0(sK3),k1_xboole_0)
% 2.70/0.99      | u1_struct_0(sK3) != X0
% 2.70/0.99      | k1_xboole_0 != X1 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_2067]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3058,plain,
% 2.70/0.99      ( r1_tarski(u1_struct_0(sK3),k1_xboole_0)
% 2.70/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.70/0.99      | u1_struct_0(sK3) != k1_xboole_0
% 2.70/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_3056]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3451,plain,
% 2.70/0.99      ( u1_struct_0(sK3) != k1_xboole_0 ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_2855,c_38,c_37,c_105,c_111,c_113,c_983,c_2952,c_3058]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3847,plain,
% 2.70/0.99      ( k1_relat_1(sK5) != k1_xboole_0 ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_3842,c_3451]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2738,plain,
% 2.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.70/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3571,plain,
% 2.70/0.99      ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2733,c_2738]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3845,plain,
% 2.70/0.99      ( r1_tarski(sK5,k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK4))) = iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_3842,c_3571]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3724,plain,
% 2.70/0.99      ( r1_tarski(sK5,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top
% 2.70/0.99      | sP0_iProver_split != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2739,c_2723]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3572,plain,
% 2.70/0.99      ( r1_tarski(sK5,k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5))) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_3445,c_2738]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3570,plain,
% 2.70/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2740,c_2738]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_18,plain,
% 2.70/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.70/0.99      | ~ v1_funct_1(X0)
% 2.70/0.99      | ~ v1_relat_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_726,plain,
% 2.70/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.70/0.99      | ~ v1_relat_1(X0)
% 2.70/0.99      | sK5 != X0 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_727,plain,
% 2.70/0.99      ( v1_funct_2(sK5,k1_relat_1(sK5),k2_relat_1(sK5)) | ~ v1_relat_1(sK5) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_726]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_794,plain,
% 2.70/0.99      ( v1_funct_2(sK5,k1_relat_1(sK5),k2_relat_1(sK5))
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | sK5 != X0 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_727]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_795,plain,
% 2.70/0.99      ( v1_funct_2(sK5,k1_relat_1(sK5),k2_relat_1(sK5))
% 2.70/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_794]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_827,plain,
% 2.70/0.99      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 2.70/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.70/0.99      | k2_funct_1(sK5) != sK5
% 2.70/0.99      | u1_struct_0(sK4) != k1_relat_1(sK5)
% 2.70/0.99      | u1_struct_0(sK3) != k2_relat_1(sK5)
% 2.70/0.99      | k2_relat_1(k2_funct_1(sK5)) != u1_struct_0(sK3) ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_746,c_795]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2062,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.70/0.99      | ~ sP1_iProver_split ),
% 2.70/0.99      inference(splitting,
% 2.70/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.70/0.99                [c_827]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2725,plain,
% 2.70/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.70/0.99      | sP1_iProver_split != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2062]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3310,plain,
% 2.70/0.99      ( sP1_iProver_split != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2733,c_2725]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2719,plain,
% 2.70/0.99      ( l1_orders_2(X0) != iProver_top
% 2.70/0.99      | l1_orders_2(sK2(X0)) = iProver_top
% 2.70/0.99      | v2_struct_0(X0) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1050]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_26,plain,
% 2.70/0.99      ( ~ m1_yellow_0(X0,X1)
% 2.70/0.99      | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 2.70/0.99      | ~ l1_orders_2(X1)
% 2.70/0.99      | ~ l1_orders_2(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_223,plain,
% 2.70/0.99      ( ~ l1_orders_2(X1)
% 2.70/0.99      | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 2.70/0.99      | ~ m1_yellow_0(X0,X1) ),
% 2.70/0.99      inference(global_propositional_subsumption,[status(thm)],[c_26,c_28]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_224,plain,
% 2.70/0.99      ( ~ m1_yellow_0(X0,X1)
% 2.70/0.99      | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 2.70/0.99      | ~ l1_orders_2(X1) ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_223]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1019,plain,
% 2.70/0.99      ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 2.70/0.99      | ~ l1_orders_2(X1)
% 2.70/0.99      | ~ l1_orders_2(X2)
% 2.70/0.99      | v2_struct_0(X2)
% 2.70/0.99      | X2 != X1
% 2.70/0.99      | sK2(X2) != X0 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_224,c_30]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1020,plain,
% 2.70/0.99      ( r1_tarski(u1_orders_2(sK2(X0)),u1_orders_2(X0))
% 2.70/0.99      | ~ l1_orders_2(X0)
% 2.70/0.99      | v2_struct_0(X0) ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_1019]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2721,plain,
% 2.70/0.99      ( r1_tarski(u1_orders_2(sK2(X0)),u1_orders_2(X0)) = iProver_top
% 2.70/0.99      | l1_orders_2(X0) != iProver_top
% 2.70/0.99      | v2_struct_0(X0) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2734,plain,
% 2.70/0.99      ( l1_orders_2(X0) != iProver_top
% 2.70/0.99      | v2_struct_0(X0) = iProver_top
% 2.70/0.99      | v2_struct_0(sK2(X0)) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2732,plain,
% 2.70/0.99      ( l1_orders_2(sK4) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2731,plain,
% 2.70/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2730,plain,
% 2.70/0.99      ( l1_orders_2(sK3) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2729,plain,
% 2.70/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_23,plain,
% 2.70/0.99      ( sK1(X0) != k1_xboole_0 | k3_tarski(X0) = k1_xboole_0 ),
% 2.70/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  % SZS output end Saturation for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  ------                               Statistics
% 2.70/0.99  
% 2.70/0.99  ------ General
% 2.70/0.99  
% 2.70/0.99  abstr_ref_over_cycles:                  0
% 2.70/0.99  abstr_ref_under_cycles:                 0
% 2.70/0.99  gc_basic_clause_elim:                   0
% 2.70/0.99  forced_gc_time:                         0
% 2.70/0.99  parsing_time:                           0.009
% 2.70/0.99  unif_index_cands_time:                  0.
% 2.70/0.99  unif_index_add_time:                    0.
% 2.70/0.99  orderings_time:                         0.
% 2.70/0.99  out_proof_time:                         0.
% 2.70/0.99  total_time:                             0.168
% 2.70/0.99  num_of_symbols:                         63
% 2.70/0.99  num_of_terms:                           4113
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing
% 2.70/0.99  
% 2.70/0.99  num_of_splits:                          2
% 2.70/0.99  num_of_split_atoms:                     2
% 2.70/0.99  num_of_reused_defs:                     0
% 2.70/0.99  num_eq_ax_congr_red:                    29
% 2.70/0.99  num_of_sem_filtered_clauses:            1
% 2.70/0.99  num_of_subtypes:                        0
% 2.70/0.99  monotx_restored_types:                  0
% 2.70/0.99  sat_num_of_epr_types:                   0
% 2.70/0.99  sat_num_of_non_cyclic_types:            0
% 2.70/0.99  sat_guarded_non_collapsed_types:        0
% 2.70/0.99  num_pure_diseq_elim:                    0
% 2.70/0.99  simp_replaced_by:                       0
% 2.70/0.99  res_preprocessed:                       154
% 2.70/0.99  prep_upred:                             0
% 2.70/0.99  prep_unflattend:                        99
% 2.70/0.99  smt_new_axioms:                         0
% 2.70/0.99  pred_elim_cands:                        5
% 2.70/0.99  pred_elim:                              9
% 2.70/0.99  pred_elim_cl:                           11
% 2.70/0.99  pred_elim_cycles:                       14
% 2.70/0.99  merged_defs:                            16
% 2.70/0.99  merged_defs_ncl:                        0
% 2.70/0.99  bin_hyper_res:                          16
% 2.70/0.99  prep_cycles:                            4
% 2.70/0.99  pred_elim_time:                         0.024
% 2.70/0.99  splitting_time:                         0.
% 2.70/0.99  sem_filter_time:                        0.
% 2.70/0.99  monotx_time:                            0.
% 2.70/0.99  subtype_inf_time:                       0.
% 2.70/0.99  
% 2.70/0.99  ------ Problem properties
% 2.70/0.99  
% 2.70/0.99  clauses:                                29
% 2.70/0.99  conjectures:                            5
% 2.70/0.99  epr:                                    4
% 2.70/0.99  horn:                                   22
% 2.70/0.99  ground:                                 9
% 2.70/0.99  unary:                                  7
% 2.70/0.99  binary:                                 11
% 2.70/0.99  lits:                                   67
% 2.70/0.99  lits_eq:                                20
% 2.70/0.99  fd_pure:                                0
% 2.70/0.99  fd_pseudo:                              0
% 2.70/0.99  fd_cond:                                1
% 2.70/0.99  fd_pseudo_cond:                         2
% 2.70/0.99  ac_symbols:                             0
% 2.70/0.99  
% 2.70/0.99  ------ Propositional Solver
% 2.70/0.99  
% 2.70/0.99  prop_solver_calls:                      28
% 2.70/0.99  prop_fast_solver_calls:                 1149
% 2.70/0.99  smt_solver_calls:                       0
% 2.70/0.99  smt_fast_solver_calls:                  0
% 2.70/0.99  prop_num_of_clauses:                    1825
% 2.70/0.99  prop_preprocess_simplified:             6437
% 2.70/0.99  prop_fo_subsumed:                       16
% 2.70/0.99  prop_solver_time:                       0.
% 2.70/0.99  smt_solver_time:                        0.
% 2.70/0.99  smt_fast_solver_time:                   0.
% 2.70/0.99  prop_fast_solver_time:                  0.
% 2.70/0.99  prop_unsat_core_time:                   0.
% 2.70/0.99  
% 2.70/0.99  ------ QBF
% 2.70/0.99  
% 2.70/0.99  qbf_q_res:                              0
% 2.70/0.99  qbf_num_tautologies:                    0
% 2.70/0.99  qbf_prep_cycles:                        0
% 2.70/0.99  
% 2.70/0.99  ------ BMC1
% 2.70/0.99  
% 2.70/0.99  bmc1_current_bound:                     -1
% 2.70/0.99  bmc1_last_solved_bound:                 -1
% 2.70/0.99  bmc1_unsat_core_size:                   -1
% 2.70/0.99  bmc1_unsat_core_parents_size:           -1
% 2.70/0.99  bmc1_merge_next_fun:                    0
% 2.70/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation
% 2.70/0.99  
% 2.70/0.99  inst_num_of_clauses:                    586
% 2.70/0.99  inst_num_in_passive:                    62
% 2.70/0.99  inst_num_in_active:                     318
% 2.70/0.99  inst_num_in_unprocessed:                206
% 2.70/0.99  inst_num_of_loops:                      330
% 2.70/0.99  inst_num_of_learning_restarts:          0
% 2.70/0.99  inst_num_moves_active_passive:          9
% 2.70/0.99  inst_lit_activity:                      0
% 2.70/0.99  inst_lit_activity_moves:                0
% 2.70/0.99  inst_num_tautologies:                   0
% 2.70/0.99  inst_num_prop_implied:                  0
% 2.70/0.99  inst_num_existing_simplified:           0
% 2.70/0.99  inst_num_eq_res_simplified:             0
% 2.70/0.99  inst_num_child_elim:                    0
% 2.70/0.99  inst_num_of_dismatching_blockings:      48
% 2.70/0.99  inst_num_of_non_proper_insts:           412
% 2.70/0.99  inst_num_of_duplicates:                 0
% 2.70/0.99  inst_inst_num_from_inst_to_res:         0
% 2.70/0.99  inst_dismatching_checking_time:         0.
% 2.70/0.99  
% 2.70/0.99  ------ Resolution
% 2.70/0.99  
% 2.70/0.99  res_num_of_clauses:                     0
% 2.70/0.99  res_num_in_passive:                     0
% 2.70/0.99  res_num_in_active:                      0
% 2.70/0.99  res_num_of_loops:                       158
% 2.70/0.99  res_forward_subset_subsumed:            22
% 2.70/0.99  res_backward_subset_subsumed:           0
% 2.70/0.99  res_forward_subsumed:                   0
% 2.70/0.99  res_backward_subsumed:                  0
% 2.70/0.99  res_forward_subsumption_resolution:     1
% 2.70/0.99  res_backward_subsumption_resolution:    0
% 2.70/0.99  res_clause_to_clause_subsumption:       149
% 2.70/0.99  res_orphan_elimination:                 0
% 2.70/0.99  res_tautology_del:                      90
% 2.70/0.99  res_num_eq_res_simplified:              0
% 2.70/0.99  res_num_sel_changes:                    0
% 2.70/0.99  res_moves_from_active_to_pass:          0
% 2.70/0.99  
% 2.70/0.99  ------ Superposition
% 2.70/0.99  
% 2.70/0.99  sup_time_total:                         0.
% 2.70/0.99  sup_time_generating:                    0.
% 2.70/0.99  sup_time_sim_full:                      0.
% 2.70/0.99  sup_time_sim_immed:                     0.
% 2.70/0.99  
% 2.70/0.99  sup_num_of_clauses:                     60
% 2.70/0.99  sup_num_in_active:                      58
% 2.70/0.99  sup_num_in_passive:                     2
% 2.70/0.99  sup_num_of_loops:                       65
% 2.70/0.99  sup_fw_superposition:                   35
% 2.70/0.99  sup_bw_superposition:                   41
% 2.70/0.99  sup_immediate_simplified:               11
% 2.70/0.99  sup_given_eliminated:                   1
% 2.70/0.99  comparisons_done:                       0
% 2.70/0.99  comparisons_avoided:                    34
% 2.70/0.99  
% 2.70/0.99  ------ Simplifications
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  sim_fw_subset_subsumed:                 5
% 2.70/0.99  sim_bw_subset_subsumed:                 2
% 2.70/0.99  sim_fw_subsumed:                        4
% 2.70/0.99  sim_bw_subsumed:                        2
% 2.70/0.99  sim_fw_subsumption_res:                 1
% 2.70/0.99  sim_bw_subsumption_res:                 0
% 2.70/0.99  sim_tautology_del:                      5
% 2.70/0.99  sim_eq_tautology_del:                   16
% 2.70/0.99  sim_eq_res_simp:                        0
% 2.70/0.99  sim_fw_demodulated:                     2
% 2.70/0.99  sim_bw_demodulated:                     5
% 2.70/0.99  sim_light_normalised:                   0
% 2.70/0.99  sim_joinable_taut:                      0
% 2.70/0.99  sim_joinable_simp:                      0
% 2.70/0.99  sim_ac_normalised:                      0
% 2.70/0.99  sim_smt_subsumption:                    0
% 2.70/0.99  
%------------------------------------------------------------------------------
