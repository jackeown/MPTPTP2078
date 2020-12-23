%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:30 EST 2020

% Result     : CounterSatisfiable 1.32s
% Output     : Saturation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  212 (1430 expanded)
%              Number of clauses        :  145 ( 387 expanded)
%              Number of leaves         :   25 ( 345 expanded)
%              Depth                    :   21
%              Number of atoms          :  632 (8229 expanded)
%              Number of equality atoms :  177 (1633 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X2),X0)
                | ~ r2_hidden(X2,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X0)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X0)
              & r2_hidden(sK1(X0,X1),X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_relat_2(X0,X1)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X3),X0)
      | ~ r2_hidden(X3,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v3_orders_2(X0)
          | ~ r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v3_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0] :
      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k13_lattice3(X0,X1,X2) = X1
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k13_lattice3(X0,X1,X2) = X1
                <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k13_lattice3(X0,X1,X2) = X1
                <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k13_lattice3(X0,X1,X2) = X1
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k13_lattice3(X0,X1,X2) = X1
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) != X1 )
              & ( r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) != X1 )
              & ( r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_orders_2(X0,X2,X1)
            | k13_lattice3(X0,X1,X2) != X1 )
          & ( r1_orders_2(X0,X2,X1)
            | k13_lattice3(X0,X1,X2) = X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_orders_2(X0,sK4,X1)
          | k13_lattice3(X0,X1,sK4) != X1 )
        & ( r1_orders_2(X0,sK4,X1)
          | k13_lattice3(X0,X1,sK4) = X1 )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) != X1 )
              & ( r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r1_orders_2(X0,X2,sK3)
              | k13_lattice3(X0,sK3,X2) != sK3 )
            & ( r1_orders_2(X0,X2,sK3)
              | k13_lattice3(X0,sK3,X2) = sK3 )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(X0,X2,X1)
                  | k13_lattice3(X0,X1,X2) != X1 )
                & ( r1_orders_2(X0,X2,X1)
                  | k13_lattice3(X0,X1,X2) = X1 )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(sK2,X2,X1)
                | k13_lattice3(sK2,X1,X2) != X1 )
              & ( r1_orders_2(sK2,X2,X1)
                | k13_lattice3(sK2,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v1_lattice3(sK2)
      & v3_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ r1_orders_2(sK2,sK4,sK3)
      | k13_lattice3(sK2,sK3,sK4) != sK3 )
    & ( r1_orders_2(sK2,sK4,sK3)
      | k13_lattice3(sK2,sK3,sK4) = sK3 )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v1_lattice3(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f44,f43,f42])).

fof(f62,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_relat_2(X0,X1)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,
    ( ~ r1_orders_2(sK2,sK4,sK3)
    | k13_lattice3(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,
    ( r1_orders_2(sK2,sK4,sK3)
    | k13_lattice3(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_286,plain,
    ( ~ v1_lattice3(X0)
    | v1_lattice3(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_285,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_284,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_283,plain,
    ( ~ v3_orders_2(X0)
    | v3_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_275,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1412,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_5,plain,
    ( r1_relat_2(X0,X1)
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1410,plain,
    ( r1_relat_2(X0_50,X1_50)
    | r2_hidden(sK1(X0_50,X1_50),X1_50)
    | ~ v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1842,plain,
    ( r1_relat_2(X0_50,X1_50) = iProver_top
    | r2_hidden(sK1(X0_50,X1_50),X1_50) = iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1410])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_708,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X2),X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_709,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X1),X1) ),
    inference(unflattening,[status(thm)],[c_708])).

cnf(c_1407,plain,
    ( ~ r2_hidden(X0_50,X1_50)
    | r2_hidden(sK0(X1_50),X1_50) ),
    inference(subtyping,[status(esa)],[c_709])).

cnf(c_1845,plain,
    ( r2_hidden(X0_50,X1_50) != iProver_top
    | r2_hidden(sK0(X1_50),X1_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1407])).

cnf(c_2375,plain,
    ( r1_relat_2(X0_50,X1_50) = iProver_top
    | r2_hidden(sK0(X1_50),X1_50) = iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_1845])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_609,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_relat_1(X2)
    | X2 != X0
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_610,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_1403,plain,
    ( ~ r2_hidden(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_610])).

cnf(c_1849,plain,
    ( r2_hidden(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1403])).

cnf(c_2520,plain,
    ( r1_relat_2(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) = iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(sK0(k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_1849])).

cnf(c_6,plain,
    ( ~ r1_relat_2(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X2),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1409,plain,
    ( ~ r1_relat_2(X0_50,X1_50)
    | ~ r2_hidden(X2_50,X1_50)
    | r2_hidden(k4_tarski(X2_50,X2_50),X0_50)
    | ~ v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1843,plain,
    ( r1_relat_2(X0_50,X1_50) != iProver_top
    | r2_hidden(X2_50,X1_50) != iProver_top
    | r2_hidden(k4_tarski(X2_50,X2_50),X0_50) = iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1409])).

cnf(c_2609,plain,
    ( r2_hidden(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | r2_hidden(k4_tarski(X0_50,X0_50),X3_50) = iProver_top
    | v1_relat_1(X3_50) != iProver_top
    | v1_relat_1(sK0(k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2520,c_1843])).

cnf(c_2451,plain,
    ( r1_relat_2(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) = iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(sK1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_1849])).

cnf(c_10,plain,
    ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_338,plain,
    ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_339,plain,
    ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_46,plain,
    ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ v3_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_341,plain,
    ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_22,c_20,c_46])).

cnf(c_1408,plain,
    ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_341])).

cnf(c_1844,plain,
    ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1408])).

cnf(c_2228,plain,
    ( r2_hidden(X0_50,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k4_tarski(X0_50,X0_50),u1_orders_2(sK2)) = iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1844,c_1843])).

cnf(c_23,plain,
    ( v3_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_45,plain,
    ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v3_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_47,plain,
    ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) = iProver_top
    | l1_orders_2(sK2) != iProver_top
    | v3_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_1413,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1960,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1413])).

cnf(c_14,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_402,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_403,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_677,plain,
    ( v1_relat_1(X0)
    | u1_orders_2(sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution_lifted,[status(thm)],[c_7,c_403])).

cnf(c_678,plain,
    ( v1_relat_1(u1_orders_2(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_1398,plain,
    ( v1_relat_1(u1_orders_2(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_678])).

cnf(c_1961,plain,
    ( v1_relat_1(u1_orders_2(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_1962,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
    | v1_relat_1(u1_orders_2(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1961])).

cnf(c_2020,plain,
    ( ~ r1_relat_2(u1_orders_2(sK2),X0_50)
    | ~ r2_hidden(X1_50,X0_50)
    | r2_hidden(k4_tarski(X1_50,X1_50),u1_orders_2(sK2))
    | ~ v1_relat_1(u1_orders_2(sK2)) ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_2164,plain,
    ( ~ r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2))
    | ~ r2_hidden(X0_50,u1_struct_0(sK2))
    | r2_hidden(k4_tarski(X0_50,X0_50),u1_orders_2(sK2))
    | ~ v1_relat_1(u1_orders_2(sK2)) ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_2165,plain,
    ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_50,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k4_tarski(X0_50,X0_50),u1_orders_2(sK2)) = iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2164])).

cnf(c_2233,plain,
    ( r2_hidden(k4_tarski(X0_50,X0_50),u1_orders_2(sK2)) = iProver_top
    | r2_hidden(X0_50,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2228,c_23,c_25,c_47,c_1960,c_1962,c_2165])).

cnf(c_2234,plain,
    ( r2_hidden(X0_50,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k4_tarski(X0_50,X0_50),u1_orders_2(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2233])).

cnf(c_2376,plain,
    ( r2_hidden(X0_50,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(u1_orders_2(sK2)),u1_orders_2(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2234,c_1845])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_311,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_312,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_31,plain,
    ( ~ v1_lattice3(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_314,plain,
    ( ~ v2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_21,c_20,c_31])).

cnf(c_324,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_314])).

cnf(c_325,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_13,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_37,plain,
    ( ~ l1_orders_2(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_50,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_327,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_21,c_20,c_31,c_37,c_50])).

cnf(c_375,plain,
    ( r2_hidden(sK0(X0),X0)
    | u1_struct_0(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_327])).

cnf(c_376,plain,
    ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_377,plain,
    ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_2155,plain,
    ( ~ r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2))
    | r2_hidden(k4_tarski(sK0(u1_struct_0(sK2)),sK0(u1_struct_0(sK2))),u1_orders_2(sK2))
    | ~ r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ v1_relat_1(u1_orders_2(sK2)) ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_2156,plain,
    ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(u1_struct_0(sK2)),sK0(u1_struct_0(sK2))),u1_orders_2(sK2)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2155])).

cnf(c_2168,plain,
    ( ~ r2_hidden(k4_tarski(sK0(u1_struct_0(sK2)),sK0(u1_struct_0(sK2))),u1_orders_2(sK2))
    | r2_hidden(sK0(u1_orders_2(sK2)),u1_orders_2(sK2)) ),
    inference(instantiation,[status(thm)],[c_1407])).

cnf(c_2169,plain,
    ( r2_hidden(k4_tarski(sK0(u1_struct_0(sK2)),sK0(u1_struct_0(sK2))),u1_orders_2(sK2)) != iProver_top
    | r2_hidden(sK0(u1_orders_2(sK2)),u1_orders_2(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2168])).

cnf(c_2441,plain,
    ( r2_hidden(sK0(u1_orders_2(sK2)),u1_orders_2(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2376,c_23,c_25,c_47,c_377,c_1960,c_1962,c_2156,c_2169])).

cnf(c_4,plain,
    ( r1_relat_2(X0,X1)
    | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1411,plain,
    ( r1_relat_2(X0_50,X1_50)
    | ~ r2_hidden(k4_tarski(sK1(X0_50,X1_50),sK1(X0_50,X1_50)),X0_50)
    | ~ v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1841,plain,
    ( r1_relat_2(X0_50,X1_50) = iProver_top
    | r2_hidden(k4_tarski(sK1(X0_50,X1_50),sK1(X0_50,X1_50)),X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1411])).

cnf(c_2241,plain,
    ( r1_relat_2(u1_orders_2(sK2),X0_50) = iProver_top
    | r2_hidden(sK1(u1_orders_2(sK2),X0_50),u1_struct_0(sK2)) != iProver_top
    | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2234,c_1841])).

cnf(c_2309,plain,
    ( r2_hidden(sK1(u1_orders_2(sK2),X0_50),u1_struct_0(sK2)) != iProver_top
    | r1_relat_2(u1_orders_2(sK2),X0_50) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2241,c_1960,c_1962])).

cnf(c_2310,plain,
    ( r1_relat_2(u1_orders_2(sK2),X0_50) = iProver_top
    | r2_hidden(sK1(u1_orders_2(sK2),X0_50),u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2309])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_643,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | u1_orders_2(sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_403])).

cnf(c_644,plain,
    ( r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_725,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_644])).

cnf(c_726,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_1397,plain,
    ( ~ r2_hidden(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_726])).

cnf(c_1855,plain,
    ( r2_hidden(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1397])).

cnf(c_2304,plain,
    ( r1_relat_2(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_1855])).

cnf(c_1854,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | v1_relat_1(u1_orders_2(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1398])).

cnf(c_2043,plain,
    ( v1_relat_1(u1_orders_2(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1854,c_1960,c_1962])).

cnf(c_737,plain,
    ( r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != u1_struct_0(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_327,c_644])).

cnf(c_1396,plain,
    ( r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_737])).

cnf(c_1856,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != u1_struct_0(sK2)
    | r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1396])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_665,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != u1_struct_0(sK2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_666,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_665])).

cnf(c_1399,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_666])).

cnf(c_1853,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != u1_struct_0(sK2)
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1399])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_653,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != u1_struct_0(sK2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_654,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_1400,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_654])).

cnf(c_1852,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != u1_struct_0(sK2)
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1400])).

cnf(c_16,negated_conjecture,
    ( ~ r1_orders_2(sK2,sK4,sK3)
    | k13_lattice3(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_176,plain,
    ( ~ r1_orders_2(sK2,sK4,sK3)
    | k13_lattice3(sK2,sK3,sK4) != sK3 ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_427,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_428,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
    | k13_lattice3(sK2,sK3,sK4) != sK3
    | sK3 != X1
    | sK4 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_176,c_428])).

cnf(c_589,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
    | k13_lattice3(sK2,sK3,sK4) != sK3 ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_591,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
    | k13_lattice3(sK2,sK3,sK4) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_589,c_19,c_18])).

cnf(c_1043,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
    | k13_lattice3(sK2,sK3,sK4) != sK3 ),
    inference(prop_impl,[status(thm)],[c_19,c_18,c_589])).

cnf(c_1404,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
    | k13_lattice3(sK2,sK3,sK4) != sK3 ),
    inference(subtyping,[status(esa)],[c_1043])).

cnf(c_1848,plain,
    ( k13_lattice3(sK2,sK3,sK4) != sK3
    | r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1404])).

cnf(c_17,negated_conjecture,
    ( r1_orders_2(sK2,sK4,sK3)
    | k13_lattice3(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_178,plain,
    ( r1_orders_2(sK2,sK4,sK3)
    | k13_lattice3(sK2,sK3,sK4) = sK3 ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_409,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_410,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
    | k13_lattice3(sK2,sK3,sK4) = sK3
    | sK3 != X1
    | sK4 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_410])).

cnf(c_575,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
    | k13_lattice3(sK2,sK3,sK4) = sK3 ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_577,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
    | k13_lattice3(sK2,sK3,sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_575,c_19,c_18])).

cnf(c_1045,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
    | k13_lattice3(sK2,sK3,sK4) = sK3 ),
    inference(prop_impl,[status(thm)],[c_19,c_18,c_575])).

cnf(c_1405,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
    | k13_lattice3(sK2,sK3,sK4) = sK3 ),
    inference(subtyping,[status(esa)],[c_1045])).

cnf(c_1847,plain,
    ( k13_lattice3(sK2,sK3,sK4) = sK3
    | r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1405])).

cnf(c_632,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | u1_struct_0(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_633,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_635,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_21,c_20,c_31,c_37,c_50])).

cnf(c_1401,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_635])).

cnf(c_1851,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1401])).

cnf(c_621,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | u1_struct_0(sK2) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_622,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_624,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_21,c_20,c_31,c_37,c_50])).

cnf(c_1402,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_624])).

cnf(c_1850,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1402])).

cnf(c_718,plain,
    ( r2_hidden(sK0(X0),X0)
    | u1_struct_0(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_327])).

cnf(c_719,plain,
    ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_1406,plain,
    ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_719])).

cnf(c_1846,plain,
    ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1406])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.32/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.32/1.00  
% 1.32/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.32/1.00  
% 1.32/1.00  ------  iProver source info
% 1.32/1.00  
% 1.32/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.32/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.32/1.00  git: non_committed_changes: false
% 1.32/1.00  git: last_make_outside_of_git: false
% 1.32/1.00  
% 1.32/1.00  ------ 
% 1.32/1.00  
% 1.32/1.00  ------ Input Options
% 1.32/1.00  
% 1.32/1.00  --out_options                           all
% 1.32/1.00  --tptp_safe_out                         true
% 1.32/1.00  --problem_path                          ""
% 1.32/1.00  --include_path                          ""
% 1.32/1.00  --clausifier                            res/vclausify_rel
% 1.32/1.00  --clausifier_options                    --mode clausify
% 1.32/1.00  --stdin                                 false
% 1.32/1.00  --stats_out                             all
% 1.32/1.00  
% 1.32/1.00  ------ General Options
% 1.32/1.00  
% 1.32/1.00  --fof                                   false
% 1.32/1.00  --time_out_real                         305.
% 1.32/1.00  --time_out_virtual                      -1.
% 1.32/1.00  --symbol_type_check                     false
% 1.32/1.00  --clausify_out                          false
% 1.32/1.00  --sig_cnt_out                           false
% 1.32/1.00  --trig_cnt_out                          false
% 1.32/1.00  --trig_cnt_out_tolerance                1.
% 1.32/1.00  --trig_cnt_out_sk_spl                   false
% 1.32/1.00  --abstr_cl_out                          false
% 1.32/1.00  
% 1.32/1.00  ------ Global Options
% 1.32/1.00  
% 1.32/1.00  --schedule                              default
% 1.32/1.00  --add_important_lit                     false
% 1.32/1.00  --prop_solver_per_cl                    1000
% 1.32/1.00  --min_unsat_core                        false
% 1.32/1.00  --soft_assumptions                      false
% 1.32/1.00  --soft_lemma_size                       3
% 1.32/1.00  --prop_impl_unit_size                   0
% 1.32/1.00  --prop_impl_unit                        []
% 1.32/1.00  --share_sel_clauses                     true
% 1.32/1.00  --reset_solvers                         false
% 1.32/1.00  --bc_imp_inh                            [conj_cone]
% 1.32/1.00  --conj_cone_tolerance                   3.
% 1.32/1.00  --extra_neg_conj                        none
% 1.32/1.00  --large_theory_mode                     true
% 1.32/1.00  --prolific_symb_bound                   200
% 1.32/1.00  --lt_threshold                          2000
% 1.32/1.00  --clause_weak_htbl                      true
% 1.32/1.00  --gc_record_bc_elim                     false
% 1.32/1.00  
% 1.32/1.00  ------ Preprocessing Options
% 1.32/1.00  
% 1.32/1.00  --preprocessing_flag                    true
% 1.32/1.00  --time_out_prep_mult                    0.1
% 1.32/1.00  --splitting_mode                        input
% 1.32/1.00  --splitting_grd                         true
% 1.32/1.00  --splitting_cvd                         false
% 1.32/1.00  --splitting_cvd_svl                     false
% 1.32/1.00  --splitting_nvd                         32
% 1.32/1.00  --sub_typing                            true
% 1.32/1.00  --prep_gs_sim                           true
% 1.32/1.00  --prep_unflatten                        true
% 1.32/1.00  --prep_res_sim                          true
% 1.32/1.00  --prep_upred                            true
% 1.32/1.00  --prep_sem_filter                       exhaustive
% 1.32/1.00  --prep_sem_filter_out                   false
% 1.32/1.00  --pred_elim                             true
% 1.32/1.00  --res_sim_input                         true
% 1.32/1.00  --eq_ax_congr_red                       true
% 1.32/1.00  --pure_diseq_elim                       true
% 1.32/1.00  --brand_transform                       false
% 1.32/1.00  --non_eq_to_eq                          false
% 1.32/1.00  --prep_def_merge                        true
% 1.32/1.00  --prep_def_merge_prop_impl              false
% 1.32/1.00  --prep_def_merge_mbd                    true
% 1.32/1.00  --prep_def_merge_tr_red                 false
% 1.32/1.00  --prep_def_merge_tr_cl                  false
% 1.32/1.00  --smt_preprocessing                     true
% 1.32/1.00  --smt_ac_axioms                         fast
% 1.32/1.00  --preprocessed_out                      false
% 1.32/1.00  --preprocessed_stats                    false
% 1.32/1.00  
% 1.32/1.00  ------ Abstraction refinement Options
% 1.32/1.00  
% 1.32/1.00  --abstr_ref                             []
% 1.32/1.00  --abstr_ref_prep                        false
% 1.32/1.00  --abstr_ref_until_sat                   false
% 1.32/1.00  --abstr_ref_sig_restrict                funpre
% 1.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.32/1.00  --abstr_ref_under                       []
% 1.32/1.00  
% 1.32/1.00  ------ SAT Options
% 1.32/1.00  
% 1.32/1.00  --sat_mode                              false
% 1.32/1.00  --sat_fm_restart_options                ""
% 1.32/1.00  --sat_gr_def                            false
% 1.32/1.00  --sat_epr_types                         true
% 1.32/1.00  --sat_non_cyclic_types                  false
% 1.32/1.00  --sat_finite_models                     false
% 1.32/1.00  --sat_fm_lemmas                         false
% 1.32/1.00  --sat_fm_prep                           false
% 1.32/1.00  --sat_fm_uc_incr                        true
% 1.32/1.00  --sat_out_model                         small
% 1.32/1.00  --sat_out_clauses                       false
% 1.32/1.00  
% 1.32/1.00  ------ QBF Options
% 1.32/1.00  
% 1.32/1.00  --qbf_mode                              false
% 1.32/1.00  --qbf_elim_univ                         false
% 1.32/1.00  --qbf_dom_inst                          none
% 1.32/1.00  --qbf_dom_pre_inst                      false
% 1.32/1.00  --qbf_sk_in                             false
% 1.32/1.00  --qbf_pred_elim                         true
% 1.32/1.00  --qbf_split                             512
% 1.32/1.00  
% 1.32/1.00  ------ BMC1 Options
% 1.32/1.00  
% 1.32/1.00  --bmc1_incremental                      false
% 1.32/1.00  --bmc1_axioms                           reachable_all
% 1.32/1.00  --bmc1_min_bound                        0
% 1.32/1.00  --bmc1_max_bound                        -1
% 1.32/1.00  --bmc1_max_bound_default                -1
% 1.32/1.00  --bmc1_symbol_reachability              true
% 1.32/1.00  --bmc1_property_lemmas                  false
% 1.32/1.00  --bmc1_k_induction                      false
% 1.32/1.00  --bmc1_non_equiv_states                 false
% 1.32/1.00  --bmc1_deadlock                         false
% 1.32/1.00  --bmc1_ucm                              false
% 1.32/1.00  --bmc1_add_unsat_core                   none
% 1.32/1.00  --bmc1_unsat_core_children              false
% 1.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.32/1.00  --bmc1_out_stat                         full
% 1.32/1.00  --bmc1_ground_init                      false
% 1.32/1.00  --bmc1_pre_inst_next_state              false
% 1.32/1.00  --bmc1_pre_inst_state                   false
% 1.32/1.00  --bmc1_pre_inst_reach_state             false
% 1.32/1.00  --bmc1_out_unsat_core                   false
% 1.32/1.00  --bmc1_aig_witness_out                  false
% 1.32/1.00  --bmc1_verbose                          false
% 1.32/1.00  --bmc1_dump_clauses_tptp                false
% 1.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.32/1.00  --bmc1_dump_file                        -
% 1.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.32/1.00  --bmc1_ucm_extend_mode                  1
% 1.32/1.00  --bmc1_ucm_init_mode                    2
% 1.32/1.00  --bmc1_ucm_cone_mode                    none
% 1.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.32/1.00  --bmc1_ucm_relax_model                  4
% 1.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.32/1.00  --bmc1_ucm_layered_model                none
% 1.32/1.00  --bmc1_ucm_max_lemma_size               10
% 1.32/1.00  
% 1.32/1.00  ------ AIG Options
% 1.32/1.00  
% 1.32/1.00  --aig_mode                              false
% 1.32/1.00  
% 1.32/1.00  ------ Instantiation Options
% 1.32/1.00  
% 1.32/1.00  --instantiation_flag                    true
% 1.32/1.00  --inst_sos_flag                         false
% 1.32/1.00  --inst_sos_phase                        true
% 1.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.32/1.00  --inst_lit_sel_side                     num_symb
% 1.32/1.00  --inst_solver_per_active                1400
% 1.32/1.00  --inst_solver_calls_frac                1.
% 1.32/1.00  --inst_passive_queue_type               priority_queues
% 1.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.32/1.00  --inst_passive_queues_freq              [25;2]
% 1.32/1.00  --inst_dismatching                      true
% 1.32/1.00  --inst_eager_unprocessed_to_passive     true
% 1.32/1.00  --inst_prop_sim_given                   true
% 1.32/1.00  --inst_prop_sim_new                     false
% 1.32/1.00  --inst_subs_new                         false
% 1.32/1.00  --inst_eq_res_simp                      false
% 1.32/1.00  --inst_subs_given                       false
% 1.32/1.00  --inst_orphan_elimination               true
% 1.32/1.00  --inst_learning_loop_flag               true
% 1.32/1.00  --inst_learning_start                   3000
% 1.32/1.00  --inst_learning_factor                  2
% 1.32/1.00  --inst_start_prop_sim_after_learn       3
% 1.32/1.00  --inst_sel_renew                        solver
% 1.32/1.00  --inst_lit_activity_flag                true
% 1.32/1.00  --inst_restr_to_given                   false
% 1.32/1.00  --inst_activity_threshold               500
% 1.32/1.00  --inst_out_proof                        true
% 1.32/1.00  
% 1.32/1.00  ------ Resolution Options
% 1.32/1.00  
% 1.32/1.00  --resolution_flag                       true
% 1.32/1.00  --res_lit_sel                           adaptive
% 1.32/1.00  --res_lit_sel_side                      none
% 1.32/1.00  --res_ordering                          kbo
% 1.32/1.00  --res_to_prop_solver                    active
% 1.32/1.00  --res_prop_simpl_new                    false
% 1.32/1.00  --res_prop_simpl_given                  true
% 1.32/1.00  --res_passive_queue_type                priority_queues
% 1.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.32/1.00  --res_passive_queues_freq               [15;5]
% 1.32/1.00  --res_forward_subs                      full
% 1.32/1.00  --res_backward_subs                     full
% 1.32/1.00  --res_forward_subs_resolution           true
% 1.32/1.00  --res_backward_subs_resolution          true
% 1.32/1.00  --res_orphan_elimination                true
% 1.32/1.00  --res_time_limit                        2.
% 1.32/1.00  --res_out_proof                         true
% 1.32/1.00  
% 1.32/1.00  ------ Superposition Options
% 1.32/1.00  
% 1.32/1.00  --superposition_flag                    true
% 1.32/1.00  --sup_passive_queue_type                priority_queues
% 1.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.32/1.00  --demod_completeness_check              fast
% 1.32/1.00  --demod_use_ground                      true
% 1.32/1.00  --sup_to_prop_solver                    passive
% 1.32/1.00  --sup_prop_simpl_new                    true
% 1.32/1.00  --sup_prop_simpl_given                  true
% 1.32/1.00  --sup_fun_splitting                     false
% 1.32/1.00  --sup_smt_interval                      50000
% 1.32/1.00  
% 1.32/1.00  ------ Superposition Simplification Setup
% 1.32/1.00  
% 1.32/1.00  --sup_indices_passive                   []
% 1.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.00  --sup_full_bw                           [BwDemod]
% 1.32/1.00  --sup_immed_triv                        [TrivRules]
% 1.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.00  --sup_immed_bw_main                     []
% 1.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/1.00  
% 1.32/1.00  ------ Combination Options
% 1.32/1.00  
% 1.32/1.00  --comb_res_mult                         3
% 1.32/1.00  --comb_sup_mult                         2
% 1.32/1.00  --comb_inst_mult                        10
% 1.32/1.00  
% 1.32/1.00  ------ Debug Options
% 1.32/1.00  
% 1.32/1.00  --dbg_backtrace                         false
% 1.32/1.00  --dbg_dump_prop_clauses                 false
% 1.32/1.00  --dbg_dump_prop_clauses_file            -
% 1.32/1.00  --dbg_out_stat                          false
% 1.32/1.00  ------ Parsing...
% 1.32/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.32/1.00  
% 1.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.32/1.00  
% 1.32/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.32/1.00  
% 1.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.32/1.00  ------ Proving...
% 1.32/1.00  ------ Problem Properties 
% 1.32/1.00  
% 1.32/1.00  
% 1.32/1.00  clauses                                 16
% 1.32/1.00  conjectures                             0
% 1.32/1.00  EPR                                     0
% 1.32/1.00  Horn                                    14
% 1.32/1.00  unary                                   4
% 1.32/1.00  binary                                  9
% 1.32/1.00  lits                                    32
% 1.32/1.00  lits eq                                 6
% 1.32/1.00  fd_pure                                 0
% 1.32/1.00  fd_pseudo                               0
% 1.32/1.00  fd_cond                                 0
% 1.32/1.00  fd_pseudo_cond                          0
% 1.32/1.00  AC symbols                              0
% 1.32/1.00  
% 1.32/1.00  ------ Schedule dynamic 5 is on 
% 1.32/1.00  
% 1.32/1.00  ------ no conjectures: strip conj schedule 
% 1.32/1.00  
% 1.32/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.32/1.00  
% 1.32/1.00  
% 1.32/1.00  ------ 
% 1.32/1.00  Current options:
% 1.32/1.00  ------ 
% 1.32/1.00  
% 1.32/1.00  ------ Input Options
% 1.32/1.00  
% 1.32/1.00  --out_options                           all
% 1.32/1.00  --tptp_safe_out                         true
% 1.32/1.00  --problem_path                          ""
% 1.32/1.00  --include_path                          ""
% 1.32/1.00  --clausifier                            res/vclausify_rel
% 1.32/1.00  --clausifier_options                    --mode clausify
% 1.32/1.00  --stdin                                 false
% 1.32/1.00  --stats_out                             all
% 1.32/1.00  
% 1.32/1.00  ------ General Options
% 1.32/1.00  
% 1.32/1.00  --fof                                   false
% 1.32/1.00  --time_out_real                         305.
% 1.32/1.00  --time_out_virtual                      -1.
% 1.32/1.00  --symbol_type_check                     false
% 1.32/1.00  --clausify_out                          false
% 1.32/1.00  --sig_cnt_out                           false
% 1.32/1.00  --trig_cnt_out                          false
% 1.32/1.00  --trig_cnt_out_tolerance                1.
% 1.32/1.00  --trig_cnt_out_sk_spl                   false
% 1.32/1.00  --abstr_cl_out                          false
% 1.32/1.00  
% 1.32/1.00  ------ Global Options
% 1.32/1.00  
% 1.32/1.00  --schedule                              default
% 1.32/1.00  --add_important_lit                     false
% 1.32/1.00  --prop_solver_per_cl                    1000
% 1.32/1.00  --min_unsat_core                        false
% 1.32/1.00  --soft_assumptions                      false
% 1.32/1.00  --soft_lemma_size                       3
% 1.32/1.00  --prop_impl_unit_size                   0
% 1.32/1.00  --prop_impl_unit                        []
% 1.32/1.00  --share_sel_clauses                     true
% 1.32/1.00  --reset_solvers                         false
% 1.32/1.00  --bc_imp_inh                            [conj_cone]
% 1.32/1.00  --conj_cone_tolerance                   3.
% 1.32/1.00  --extra_neg_conj                        none
% 1.32/1.00  --large_theory_mode                     true
% 1.32/1.00  --prolific_symb_bound                   200
% 1.32/1.00  --lt_threshold                          2000
% 1.32/1.00  --clause_weak_htbl                      true
% 1.32/1.00  --gc_record_bc_elim                     false
% 1.32/1.00  
% 1.32/1.00  ------ Preprocessing Options
% 1.32/1.00  
% 1.32/1.00  --preprocessing_flag                    true
% 1.32/1.00  --time_out_prep_mult                    0.1
% 1.32/1.00  --splitting_mode                        input
% 1.32/1.00  --splitting_grd                         true
% 1.32/1.00  --splitting_cvd                         false
% 1.32/1.00  --splitting_cvd_svl                     false
% 1.32/1.00  --splitting_nvd                         32
% 1.32/1.00  --sub_typing                            true
% 1.32/1.00  --prep_gs_sim                           true
% 1.32/1.00  --prep_unflatten                        true
% 1.32/1.00  --prep_res_sim                          true
% 1.32/1.00  --prep_upred                            true
% 1.32/1.00  --prep_sem_filter                       exhaustive
% 1.32/1.00  --prep_sem_filter_out                   false
% 1.32/1.00  --pred_elim                             true
% 1.32/1.00  --res_sim_input                         true
% 1.32/1.00  --eq_ax_congr_red                       true
% 1.32/1.00  --pure_diseq_elim                       true
% 1.32/1.00  --brand_transform                       false
% 1.32/1.00  --non_eq_to_eq                          false
% 1.32/1.00  --prep_def_merge                        true
% 1.32/1.00  --prep_def_merge_prop_impl              false
% 1.32/1.00  --prep_def_merge_mbd                    true
% 1.32/1.00  --prep_def_merge_tr_red                 false
% 1.32/1.00  --prep_def_merge_tr_cl                  false
% 1.32/1.00  --smt_preprocessing                     true
% 1.32/1.00  --smt_ac_axioms                         fast
% 1.32/1.00  --preprocessed_out                      false
% 1.32/1.00  --preprocessed_stats                    false
% 1.32/1.00  
% 1.32/1.00  ------ Abstraction refinement Options
% 1.32/1.00  
% 1.32/1.00  --abstr_ref                             []
% 1.32/1.00  --abstr_ref_prep                        false
% 1.32/1.00  --abstr_ref_until_sat                   false
% 1.32/1.00  --abstr_ref_sig_restrict                funpre
% 1.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.32/1.00  --abstr_ref_under                       []
% 1.32/1.00  
% 1.32/1.00  ------ SAT Options
% 1.32/1.00  
% 1.32/1.00  --sat_mode                              false
% 1.32/1.00  --sat_fm_restart_options                ""
% 1.32/1.00  --sat_gr_def                            false
% 1.32/1.00  --sat_epr_types                         true
% 1.32/1.00  --sat_non_cyclic_types                  false
% 1.32/1.00  --sat_finite_models                     false
% 1.32/1.00  --sat_fm_lemmas                         false
% 1.32/1.00  --sat_fm_prep                           false
% 1.32/1.00  --sat_fm_uc_incr                        true
% 1.32/1.00  --sat_out_model                         small
% 1.32/1.00  --sat_out_clauses                       false
% 1.32/1.00  
% 1.32/1.00  ------ QBF Options
% 1.32/1.00  
% 1.32/1.00  --qbf_mode                              false
% 1.32/1.00  --qbf_elim_univ                         false
% 1.32/1.00  --qbf_dom_inst                          none
% 1.32/1.00  --qbf_dom_pre_inst                      false
% 1.32/1.00  --qbf_sk_in                             false
% 1.32/1.00  --qbf_pred_elim                         true
% 1.32/1.00  --qbf_split                             512
% 1.32/1.00  
% 1.32/1.00  ------ BMC1 Options
% 1.32/1.00  
% 1.32/1.00  --bmc1_incremental                      false
% 1.32/1.00  --bmc1_axioms                           reachable_all
% 1.32/1.00  --bmc1_min_bound                        0
% 1.32/1.00  --bmc1_max_bound                        -1
% 1.32/1.00  --bmc1_max_bound_default                -1
% 1.32/1.00  --bmc1_symbol_reachability              true
% 1.32/1.00  --bmc1_property_lemmas                  false
% 1.32/1.00  --bmc1_k_induction                      false
% 1.32/1.00  --bmc1_non_equiv_states                 false
% 1.32/1.00  --bmc1_deadlock                         false
% 1.32/1.00  --bmc1_ucm                              false
% 1.32/1.00  --bmc1_add_unsat_core                   none
% 1.32/1.00  --bmc1_unsat_core_children              false
% 1.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.32/1.00  --bmc1_out_stat                         full
% 1.32/1.00  --bmc1_ground_init                      false
% 1.32/1.00  --bmc1_pre_inst_next_state              false
% 1.32/1.00  --bmc1_pre_inst_state                   false
% 1.32/1.00  --bmc1_pre_inst_reach_state             false
% 1.32/1.00  --bmc1_out_unsat_core                   false
% 1.32/1.00  --bmc1_aig_witness_out                  false
% 1.32/1.00  --bmc1_verbose                          false
% 1.32/1.00  --bmc1_dump_clauses_tptp                false
% 1.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.32/1.00  --bmc1_dump_file                        -
% 1.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.32/1.00  --bmc1_ucm_extend_mode                  1
% 1.32/1.00  --bmc1_ucm_init_mode                    2
% 1.32/1.00  --bmc1_ucm_cone_mode                    none
% 1.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.32/1.00  --bmc1_ucm_relax_model                  4
% 1.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.32/1.00  --bmc1_ucm_layered_model                none
% 1.32/1.00  --bmc1_ucm_max_lemma_size               10
% 1.32/1.00  
% 1.32/1.00  ------ AIG Options
% 1.32/1.00  
% 1.32/1.00  --aig_mode                              false
% 1.32/1.00  
% 1.32/1.00  ------ Instantiation Options
% 1.32/1.00  
% 1.32/1.00  --instantiation_flag                    true
% 1.32/1.00  --inst_sos_flag                         false
% 1.32/1.00  --inst_sos_phase                        true
% 1.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.32/1.00  --inst_lit_sel_side                     none
% 1.32/1.00  --inst_solver_per_active                1400
% 1.32/1.00  --inst_solver_calls_frac                1.
% 1.32/1.00  --inst_passive_queue_type               priority_queues
% 1.32/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.32/1.00  --inst_passive_queues_freq              [25;2]
% 1.32/1.00  --inst_dismatching                      true
% 1.32/1.00  --inst_eager_unprocessed_to_passive     true
% 1.32/1.00  --inst_prop_sim_given                   true
% 1.32/1.00  --inst_prop_sim_new                     false
% 1.32/1.00  --inst_subs_new                         false
% 1.32/1.00  --inst_eq_res_simp                      false
% 1.32/1.00  --inst_subs_given                       false
% 1.32/1.00  --inst_orphan_elimination               true
% 1.32/1.00  --inst_learning_loop_flag               true
% 1.32/1.00  --inst_learning_start                   3000
% 1.32/1.00  --inst_learning_factor                  2
% 1.32/1.00  --inst_start_prop_sim_after_learn       3
% 1.32/1.00  --inst_sel_renew                        solver
% 1.32/1.00  --inst_lit_activity_flag                true
% 1.32/1.00  --inst_restr_to_given                   false
% 1.32/1.00  --inst_activity_threshold               500
% 1.32/1.00  --inst_out_proof                        true
% 1.32/1.00  
% 1.32/1.00  ------ Resolution Options
% 1.32/1.00  
% 1.32/1.00  --resolution_flag                       false
% 1.32/1.00  --res_lit_sel                           adaptive
% 1.32/1.00  --res_lit_sel_side                      none
% 1.32/1.00  --res_ordering                          kbo
% 1.32/1.00  --res_to_prop_solver                    active
% 1.32/1.00  --res_prop_simpl_new                    false
% 1.32/1.00  --res_prop_simpl_given                  true
% 1.32/1.00  --res_passive_queue_type                priority_queues
% 1.32/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.32/1.00  --res_passive_queues_freq               [15;5]
% 1.32/1.00  --res_forward_subs                      full
% 1.32/1.00  --res_backward_subs                     full
% 1.32/1.00  --res_forward_subs_resolution           true
% 1.32/1.00  --res_backward_subs_resolution          true
% 1.32/1.00  --res_orphan_elimination                true
% 1.32/1.00  --res_time_limit                        2.
% 1.32/1.00  --res_out_proof                         true
% 1.32/1.00  
% 1.32/1.00  ------ Superposition Options
% 1.32/1.00  
% 1.32/1.00  --superposition_flag                    true
% 1.32/1.00  --sup_passive_queue_type                priority_queues
% 1.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.32/1.00  --demod_completeness_check              fast
% 1.32/1.00  --demod_use_ground                      true
% 1.32/1.00  --sup_to_prop_solver                    passive
% 1.32/1.00  --sup_prop_simpl_new                    true
% 1.32/1.00  --sup_prop_simpl_given                  true
% 1.32/1.00  --sup_fun_splitting                     false
% 1.32/1.00  --sup_smt_interval                      50000
% 1.32/1.00  
% 1.32/1.00  ------ Superposition Simplification Setup
% 1.32/1.00  
% 1.32/1.00  --sup_indices_passive                   []
% 1.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.00  --sup_full_bw                           [BwDemod]
% 1.32/1.00  --sup_immed_triv                        [TrivRules]
% 1.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.00  --sup_immed_bw_main                     []
% 1.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/1.00  
% 1.32/1.00  ------ Combination Options
% 1.32/1.00  
% 1.32/1.00  --comb_res_mult                         3
% 1.32/1.00  --comb_sup_mult                         2
% 1.32/1.00  --comb_inst_mult                        10
% 1.32/1.00  
% 1.32/1.00  ------ Debug Options
% 1.32/1.00  
% 1.32/1.00  --dbg_backtrace                         false
% 1.32/1.00  --dbg_dump_prop_clauses                 false
% 1.32/1.00  --dbg_dump_prop_clauses_file            -
% 1.32/1.00  --dbg_out_stat                          false
% 1.32/1.00  
% 1.32/1.00  
% 1.32/1.00  
% 1.32/1.00  
% 1.32/1.00  ------ Proving...
% 1.32/1.00  
% 1.32/1.00  
% 1.32/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 1.32/1.00  
% 1.32/1.00  % SZS output start Saturation for theBenchmark.p
% 1.32/1.00  
% 1.32/1.00  fof(f4,axiom,(
% 1.32/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k4_tarski(X2,X2),X0))))),
% 1.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.32/1.00  
% 1.32/1.00  fof(f18,plain,(
% 1.32/1.00    ! [X0] : (! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 1.32/1.00    inference(ennf_transformation,[],[f4])).
% 1.32/1.00  
% 1.32/1.00  fof(f34,plain,(
% 1.32/1.00    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 1.32/1.00    inference(nnf_transformation,[],[f18])).
% 1.32/1.00  
% 1.32/1.00  fof(f35,plain,(
% 1.32/1.00    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1))) & (! [X3] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 1.32/1.00    inference(rectify,[],[f34])).
% 1.32/1.00  
% 1.32/1.00  fof(f36,plain,(
% 1.32/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X0) & r2_hidden(sK1(X0,X1),X1)))),
% 1.32/1.00    introduced(choice_axiom,[])).
% 1.32/1.00  
% 1.32/1.00  fof(f37,plain,(
% 1.32/1.00    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X0) & r2_hidden(sK1(X0,X1),X1))) & (! [X3] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 1.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 1.32/1.00  
% 1.32/1.00  fof(f51,plain,(
% 1.32/1.00    ( ! [X0,X1] : (r1_relat_2(X0,X1) | r2_hidden(sK1(X0,X1),X1) | ~v1_relat_1(X0)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f37])).
% 1.32/1.00  
% 1.32/1.00  fof(f1,axiom,(
% 1.32/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.32/1.00  
% 1.32/1.00  fof(f30,plain,(
% 1.32/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.32/1.00    inference(nnf_transformation,[],[f1])).
% 1.32/1.00  
% 1.32/1.00  fof(f31,plain,(
% 1.32/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.32/1.00    inference(rectify,[],[f30])).
% 1.32/1.00  
% 1.32/1.00  fof(f32,plain,(
% 1.32/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.32/1.00    introduced(choice_axiom,[])).
% 1.32/1.00  
% 1.32/1.00  fof(f33,plain,(
% 1.32/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 1.32/1.00  
% 1.32/1.00  fof(f47,plain,(
% 1.32/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f33])).
% 1.32/1.00  
% 1.32/1.00  fof(f46,plain,(
% 1.32/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f33])).
% 1.32/1.00  
% 1.32/1.00  fof(f2,axiom,(
% 1.32/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.32/1.00  
% 1.32/1.00  fof(f15,plain,(
% 1.32/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.32/1.00    inference(ennf_transformation,[],[f2])).
% 1.32/1.00  
% 1.32/1.00  fof(f48,plain,(
% 1.32/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f15])).
% 1.32/1.00  
% 1.32/1.00  fof(f5,axiom,(
% 1.32/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.32/1.00  
% 1.32/1.00  fof(f19,plain,(
% 1.32/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/1.00    inference(ennf_transformation,[],[f5])).
% 1.32/1.00  
% 1.32/1.00  fof(f53,plain,(
% 1.32/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/1.00    inference(cnf_transformation,[],[f19])).
% 1.32/1.00  
% 1.32/1.00  fof(f50,plain,(
% 1.32/1.00    ( ! [X0,X3,X1] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1) | ~r1_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f37])).
% 1.32/1.00  
% 1.32/1.00  fof(f7,axiom,(
% 1.32/1.00    ! [X0] : (l1_orders_2(X0) => (v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 1.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.32/1.00  
% 1.32/1.00  fof(f22,plain,(
% 1.32/1.00    ! [X0] : ((v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.32/1.00    inference(ennf_transformation,[],[f7])).
% 1.32/1.00  
% 1.32/1.00  fof(f38,plain,(
% 1.32/1.00    ! [X0] : (((v3_orders_2(X0) | ~r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v3_orders_2(X0))) | ~l1_orders_2(X0))),
% 1.32/1.00    inference(nnf_transformation,[],[f22])).
% 1.32/1.00  
% 1.32/1.00  fof(f55,plain,(
% 1.32/1.00    ( ! [X0] : (r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f38])).
% 1.32/1.00  
% 1.32/1.00  fof(f12,conjecture,(
% 1.32/1.00    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X1 <=> r1_orders_2(X0,X2,X1)))))),
% 1.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.32/1.00  
% 1.32/1.00  fof(f13,negated_conjecture,(
% 1.32/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X1 <=> r1_orders_2(X0,X2,X1)))))),
% 1.32/1.00    inference(negated_conjecture,[],[f12])).
% 1.32/1.00  
% 1.32/1.00  fof(f14,plain,(
% 1.32/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X1 <=> r1_orders_2(X0,X2,X1)))))),
% 1.32/1.00    inference(pure_predicate_removal,[],[f13])).
% 1.32/1.00  
% 1.32/1.00  fof(f28,plain,(
% 1.32/1.00    ? [X0] : (? [X1] : (? [X2] : ((k13_lattice3(X0,X1,X2) = X1 <~> r1_orders_2(X0,X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v1_lattice3(X0) & v3_orders_2(X0)))),
% 1.32/1.00    inference(ennf_transformation,[],[f14])).
% 1.32/1.00  
% 1.32/1.00  fof(f29,plain,(
% 1.32/1.00    ? [X0] : (? [X1] : (? [X2] : ((k13_lattice3(X0,X1,X2) = X1 <~> r1_orders_2(X0,X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v3_orders_2(X0))),
% 1.32/1.00    inference(flattening,[],[f28])).
% 1.32/1.00  
% 1.32/1.00  fof(f40,plain,(
% 1.32/1.00    ? [X0] : (? [X1] : (? [X2] : (((~r1_orders_2(X0,X2,X1) | k13_lattice3(X0,X1,X2) != X1) & (r1_orders_2(X0,X2,X1) | k13_lattice3(X0,X1,X2) = X1)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v3_orders_2(X0))),
% 1.32/1.00    inference(nnf_transformation,[],[f29])).
% 1.32/1.00  
% 1.32/1.00  fof(f41,plain,(
% 1.32/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r1_orders_2(X0,X2,X1) | k13_lattice3(X0,X1,X2) != X1) & (r1_orders_2(X0,X2,X1) | k13_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v3_orders_2(X0))),
% 1.32/1.00    inference(flattening,[],[f40])).
% 1.32/1.00  
% 1.32/1.00  fof(f44,plain,(
% 1.32/1.00    ( ! [X0,X1] : (? [X2] : ((~r1_orders_2(X0,X2,X1) | k13_lattice3(X0,X1,X2) != X1) & (r1_orders_2(X0,X2,X1) | k13_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_orders_2(X0,sK4,X1) | k13_lattice3(X0,X1,sK4) != X1) & (r1_orders_2(X0,sK4,X1) | k13_lattice3(X0,X1,sK4) = X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.32/1.00    introduced(choice_axiom,[])).
% 1.32/1.00  
% 1.32/1.00  fof(f43,plain,(
% 1.32/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_orders_2(X0,X2,X1) | k13_lattice3(X0,X1,X2) != X1) & (r1_orders_2(X0,X2,X1) | k13_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r1_orders_2(X0,X2,sK3) | k13_lattice3(X0,sK3,X2) != sK3) & (r1_orders_2(X0,X2,sK3) | k13_lattice3(X0,sK3,X2) = sK3) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.32/1.00    introduced(choice_axiom,[])).
% 1.32/1.00  
% 1.32/1.00  fof(f42,plain,(
% 1.32/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r1_orders_2(X0,X2,X1) | k13_lattice3(X0,X1,X2) != X1) & (r1_orders_2(X0,X2,X1) | k13_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : ((~r1_orders_2(sK2,X2,X1) | k13_lattice3(sK2,X1,X2) != X1) & (r1_orders_2(sK2,X2,X1) | k13_lattice3(sK2,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v1_lattice3(sK2) & v3_orders_2(sK2))),
% 1.32/1.00    introduced(choice_axiom,[])).
% 1.32/1.00  
% 1.32/1.00  fof(f45,plain,(
% 1.32/1.00    (((~r1_orders_2(sK2,sK4,sK3) | k13_lattice3(sK2,sK3,sK4) != sK3) & (r1_orders_2(sK2,sK4,sK3) | k13_lattice3(sK2,sK3,sK4) = sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v1_lattice3(sK2) & v3_orders_2(sK2)),
% 1.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f44,f43,f42])).
% 1.32/1.00  
% 1.32/1.00  fof(f62,plain,(
% 1.32/1.00    v3_orders_2(sK2)),
% 1.32/1.00    inference(cnf_transformation,[],[f45])).
% 1.32/1.00  
% 1.32/1.00  fof(f64,plain,(
% 1.32/1.00    l1_orders_2(sK2)),
% 1.32/1.00    inference(cnf_transformation,[],[f45])).
% 1.32/1.00  
% 1.32/1.00  fof(f10,axiom,(
% 1.32/1.00    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 1.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.32/1.00  
% 1.32/1.00  fof(f25,plain,(
% 1.32/1.00    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.32/1.00    inference(ennf_transformation,[],[f10])).
% 1.32/1.00  
% 1.32/1.00  fof(f60,plain,(
% 1.32/1.00    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f25])).
% 1.32/1.00  
% 1.32/1.00  fof(f6,axiom,(
% 1.32/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.32/1.00  
% 1.32/1.00  fof(f20,plain,(
% 1.32/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.32/1.00    inference(ennf_transformation,[],[f6])).
% 1.32/1.00  
% 1.32/1.00  fof(f21,plain,(
% 1.32/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.32/1.00    inference(flattening,[],[f20])).
% 1.32/1.00  
% 1.32/1.00  fof(f54,plain,(
% 1.32/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f21])).
% 1.32/1.00  
% 1.32/1.00  fof(f11,axiom,(
% 1.32/1.00    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.32/1.00  
% 1.32/1.00  fof(f26,plain,(
% 1.32/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.32/1.00    inference(ennf_transformation,[],[f11])).
% 1.32/1.00  
% 1.32/1.00  fof(f27,plain,(
% 1.32/1.00    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.32/1.00    inference(flattening,[],[f26])).
% 1.32/1.00  
% 1.32/1.00  fof(f61,plain,(
% 1.32/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f27])).
% 1.32/1.00  
% 1.32/1.00  fof(f63,plain,(
% 1.32/1.00    v1_lattice3(sK2)),
% 1.32/1.00    inference(cnf_transformation,[],[f45])).
% 1.32/1.00  
% 1.32/1.00  fof(f9,axiom,(
% 1.32/1.00    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.32/1.00  
% 1.32/1.00  fof(f24,plain,(
% 1.32/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.32/1.00    inference(ennf_transformation,[],[f9])).
% 1.32/1.00  
% 1.32/1.00  fof(f59,plain,(
% 1.32/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f24])).
% 1.32/1.00  
% 1.32/1.00  fof(f52,plain,(
% 1.32/1.00    ( ! [X0,X1] : (r1_relat_2(X0,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f37])).
% 1.32/1.00  
% 1.32/1.00  fof(f3,axiom,(
% 1.32/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.32/1.00  
% 1.32/1.00  fof(f16,plain,(
% 1.32/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.32/1.00    inference(ennf_transformation,[],[f3])).
% 1.32/1.00  
% 1.32/1.00  fof(f17,plain,(
% 1.32/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.32/1.00    inference(flattening,[],[f16])).
% 1.32/1.00  
% 1.32/1.00  fof(f49,plain,(
% 1.32/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f17])).
% 1.32/1.00  
% 1.32/1.00  fof(f65,plain,(
% 1.32/1.00    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.32/1.00    inference(cnf_transformation,[],[f45])).
% 1.32/1.00  
% 1.32/1.00  fof(f66,plain,(
% 1.32/1.00    m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.32/1.00    inference(cnf_transformation,[],[f45])).
% 1.32/1.00  
% 1.32/1.00  fof(f68,plain,(
% 1.32/1.00    ~r1_orders_2(sK2,sK4,sK3) | k13_lattice3(sK2,sK3,sK4) != sK3),
% 1.32/1.00    inference(cnf_transformation,[],[f45])).
% 1.32/1.00  
% 1.32/1.00  fof(f8,axiom,(
% 1.32/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 1.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.32/1.00  
% 1.32/1.00  fof(f23,plain,(
% 1.32/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.32/1.00    inference(ennf_transformation,[],[f8])).
% 1.32/1.00  
% 1.32/1.00  fof(f39,plain,(
% 1.32/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.32/1.00    inference(nnf_transformation,[],[f23])).
% 1.32/1.00  
% 1.32/1.00  fof(f58,plain,(
% 1.32/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f39])).
% 1.32/1.00  
% 1.32/1.00  fof(f67,plain,(
% 1.32/1.00    r1_orders_2(sK2,sK4,sK3) | k13_lattice3(sK2,sK3,sK4) = sK3),
% 1.32/1.00    inference(cnf_transformation,[],[f45])).
% 1.32/1.00  
% 1.32/1.00  fof(f57,plain,(
% 1.32/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.32/1.00    inference(cnf_transformation,[],[f39])).
% 1.32/1.00  
% 1.32/1.00  cnf(c_286,plain,
% 1.32/1.00      ( ~ v1_lattice3(X0) | v1_lattice3(X1) | X1 != X0 ),
% 1.32/1.00      theory(equality) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_285,plain,
% 1.32/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.32/1.00      | r1_orders_2(X3,X4,X5)
% 1.32/1.00      | X3 != X0
% 1.32/1.00      | X4 != X1
% 1.32/1.00      | X5 != X2 ),
% 1.32/1.00      theory(equality) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_284,plain,
% 1.32/1.00      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 1.32/1.00      theory(equality) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_283,plain,
% 1.32/1.00      ( ~ v3_orders_2(X0) | v3_orders_2(X1) | X1 != X0 ),
% 1.32/1.00      theory(equality) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_277,plain,
% 1.32/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.32/1.00      theory(equality) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_275,plain,
% 1.32/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.32/1.00      theory(equality) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1412,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_5,plain,
% 1.32/1.00      ( r1_relat_2(X0,X1) | r2_hidden(sK1(X0,X1),X1) | ~ v1_relat_1(X0) ),
% 1.32/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1410,plain,
% 1.32/1.00      ( r1_relat_2(X0_50,X1_50)
% 1.32/1.00      | r2_hidden(sK1(X0_50,X1_50),X1_50)
% 1.32/1.00      | ~ v1_relat_1(X0_50) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1842,plain,
% 1.32/1.00      ( r1_relat_2(X0_50,X1_50) = iProver_top
% 1.32/1.00      | r2_hidden(sK1(X0_50,X1_50),X1_50) = iProver_top
% 1.32/1.00      | v1_relat_1(X0_50) != iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1410]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_0,plain,
% 1.32/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.32/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1,plain,
% 1.32/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.32/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_708,plain,
% 1.32/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(sK0(X2),X2) | X1 != X2 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_709,plain,
% 1.32/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(sK0(X1),X1) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_708]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1407,plain,
% 1.32/1.00      ( ~ r2_hidden(X0_50,X1_50) | r2_hidden(sK0(X1_50),X1_50) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_709]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1845,plain,
% 1.32/1.00      ( r2_hidden(X0_50,X1_50) != iProver_top
% 1.32/1.00      | r2_hidden(sK0(X1_50),X1_50) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1407]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2375,plain,
% 1.32/1.00      ( r1_relat_2(X0_50,X1_50) = iProver_top
% 1.32/1.00      | r2_hidden(sK0(X1_50),X1_50) = iProver_top
% 1.32/1.00      | v1_relat_1(X0_50) != iProver_top ),
% 1.32/1.00      inference(superposition,[status(thm)],[c_1842,c_1845]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2,plain,
% 1.32/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 1.32/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_7,plain,
% 1.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.32/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_609,plain,
% 1.32/1.00      ( ~ r2_hidden(X0,X1)
% 1.32/1.00      | v1_relat_1(X2)
% 1.32/1.00      | X2 != X0
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != X1 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_7]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_610,plain,
% 1.32/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_609]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1403,plain,
% 1.32/1.00      ( ~ r2_hidden(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 1.32/1.00      | v1_relat_1(X0_50) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_610]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1849,plain,
% 1.32/1.00      ( r2_hidden(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 1.32/1.00      | v1_relat_1(X0_50) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1403]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2520,plain,
% 1.32/1.00      ( r1_relat_2(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) = iProver_top
% 1.32/1.00      | v1_relat_1(X0_50) != iProver_top
% 1.32/1.00      | v1_relat_1(sK0(k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))) = iProver_top ),
% 1.32/1.00      inference(superposition,[status(thm)],[c_2375,c_1849]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_6,plain,
% 1.32/1.00      ( ~ r1_relat_2(X0,X1)
% 1.32/1.00      | ~ r2_hidden(X2,X1)
% 1.32/1.00      | r2_hidden(k4_tarski(X2,X2),X0)
% 1.32/1.00      | ~ v1_relat_1(X0) ),
% 1.32/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1409,plain,
% 1.32/1.00      ( ~ r1_relat_2(X0_50,X1_50)
% 1.32/1.00      | ~ r2_hidden(X2_50,X1_50)
% 1.32/1.00      | r2_hidden(k4_tarski(X2_50,X2_50),X0_50)
% 1.32/1.00      | ~ v1_relat_1(X0_50) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1843,plain,
% 1.32/1.00      ( r1_relat_2(X0_50,X1_50) != iProver_top
% 1.32/1.00      | r2_hidden(X2_50,X1_50) != iProver_top
% 1.32/1.00      | r2_hidden(k4_tarski(X2_50,X2_50),X0_50) = iProver_top
% 1.32/1.00      | v1_relat_1(X0_50) != iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1409]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2609,plain,
% 1.32/1.00      ( r2_hidden(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 1.32/1.00      | r2_hidden(k4_tarski(X0_50,X0_50),X3_50) = iProver_top
% 1.32/1.00      | v1_relat_1(X3_50) != iProver_top
% 1.32/1.00      | v1_relat_1(sK0(k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))) = iProver_top ),
% 1.32/1.00      inference(superposition,[status(thm)],[c_2520,c_1843]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2451,plain,
% 1.32/1.00      ( r1_relat_2(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) = iProver_top
% 1.32/1.00      | v1_relat_1(X0_50) != iProver_top
% 1.32/1.00      | v1_relat_1(sK1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))) = iProver_top ),
% 1.32/1.00      inference(superposition,[status(thm)],[c_1842,c_1849]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_10,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
% 1.32/1.00      | ~ l1_orders_2(X0)
% 1.32/1.00      | ~ v3_orders_2(X0) ),
% 1.32/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_22,negated_conjecture,
% 1.32/1.00      ( v3_orders_2(sK2) ),
% 1.32/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_338,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
% 1.32/1.00      | ~ l1_orders_2(X0)
% 1.32/1.00      | sK2 != X0 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_339,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) | ~ l1_orders_2(sK2) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_338]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_20,negated_conjecture,
% 1.32/1.00      ( l1_orders_2(sK2) ),
% 1.32/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_46,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2))
% 1.32/1.00      | ~ l1_orders_2(sK2)
% 1.32/1.00      | ~ v3_orders_2(sK2) ),
% 1.32/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_341,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) ),
% 1.32/1.00      inference(global_propositional_subsumption,
% 1.32/1.00                [status(thm)],
% 1.32/1.00                [c_339,c_22,c_20,c_46]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1408,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_341]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1844,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1408]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2228,plain,
% 1.32/1.00      ( r2_hidden(X0_50,u1_struct_0(sK2)) != iProver_top
% 1.32/1.00      | r2_hidden(k4_tarski(X0_50,X0_50),u1_orders_2(sK2)) = iProver_top
% 1.32/1.00      | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
% 1.32/1.00      inference(superposition,[status(thm)],[c_1844,c_1843]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_23,plain,
% 1.32/1.00      ( v3_orders_2(sK2) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_25,plain,
% 1.32/1.00      ( l1_orders_2(sK2) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_45,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) = iProver_top
% 1.32/1.00      | l1_orders_2(X0) != iProver_top
% 1.32/1.00      | v3_orders_2(X0) != iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_47,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) = iProver_top
% 1.32/1.00      | l1_orders_2(sK2) != iProver_top
% 1.32/1.00      | v3_orders_2(sK2) != iProver_top ),
% 1.32/1.00      inference(instantiation,[status(thm)],[c_45]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1413,plain,( X0_50 = X0_50 ),theory(equality) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1960,plain,
% 1.32/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
% 1.32/1.00      inference(instantiation,[status(thm)],[c_1413]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_14,plain,
% 1.32/1.00      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.32/1.00      | ~ l1_orders_2(X0) ),
% 1.32/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_402,plain,
% 1.32/1.00      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.32/1.00      | sK2 != X0 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_403,plain,
% 1.32/1.00      ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_402]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_677,plain,
% 1.32/1.00      ( v1_relat_1(X0)
% 1.32/1.00      | u1_orders_2(sK2) != X0
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_403]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_678,plain,
% 1.32/1.00      ( v1_relat_1(u1_orders_2(sK2))
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_677]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1398,plain,
% 1.32/1.00      ( v1_relat_1(u1_orders_2(sK2))
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_678]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1961,plain,
% 1.32/1.00      ( v1_relat_1(u1_orders_2(sK2))
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
% 1.32/1.00      inference(instantiation,[status(thm)],[c_1398]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1962,plain,
% 1.32/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
% 1.32/1.00      | v1_relat_1(u1_orders_2(sK2)) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1961]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2020,plain,
% 1.32/1.00      ( ~ r1_relat_2(u1_orders_2(sK2),X0_50)
% 1.32/1.00      | ~ r2_hidden(X1_50,X0_50)
% 1.32/1.00      | r2_hidden(k4_tarski(X1_50,X1_50),u1_orders_2(sK2))
% 1.32/1.00      | ~ v1_relat_1(u1_orders_2(sK2)) ),
% 1.32/1.00      inference(instantiation,[status(thm)],[c_1409]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2164,plain,
% 1.32/1.00      ( ~ r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2))
% 1.32/1.00      | ~ r2_hidden(X0_50,u1_struct_0(sK2))
% 1.32/1.00      | r2_hidden(k4_tarski(X0_50,X0_50),u1_orders_2(sK2))
% 1.32/1.00      | ~ v1_relat_1(u1_orders_2(sK2)) ),
% 1.32/1.00      inference(instantiation,[status(thm)],[c_2020]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2165,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) != iProver_top
% 1.32/1.00      | r2_hidden(X0_50,u1_struct_0(sK2)) != iProver_top
% 1.32/1.00      | r2_hidden(k4_tarski(X0_50,X0_50),u1_orders_2(sK2)) = iProver_top
% 1.32/1.00      | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2164]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2233,plain,
% 1.32/1.00      ( r2_hidden(k4_tarski(X0_50,X0_50),u1_orders_2(sK2)) = iProver_top
% 1.32/1.00      | r2_hidden(X0_50,u1_struct_0(sK2)) != iProver_top ),
% 1.32/1.00      inference(global_propositional_subsumption,
% 1.32/1.00                [status(thm)],
% 1.32/1.00                [c_2228,c_23,c_25,c_47,c_1960,c_1962,c_2165]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2234,plain,
% 1.32/1.00      ( r2_hidden(X0_50,u1_struct_0(sK2)) != iProver_top
% 1.32/1.00      | r2_hidden(k4_tarski(X0_50,X0_50),u1_orders_2(sK2)) = iProver_top ),
% 1.32/1.00      inference(renaming,[status(thm)],[c_2233]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2376,plain,
% 1.32/1.00      ( r2_hidden(X0_50,u1_struct_0(sK2)) != iProver_top
% 1.32/1.00      | r2_hidden(sK0(u1_orders_2(sK2)),u1_orders_2(sK2)) = iProver_top ),
% 1.32/1.00      inference(superposition,[status(thm)],[c_2234,c_1845]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_8,plain,
% 1.32/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.32/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_15,plain,
% 1.32/1.00      ( ~ v1_lattice3(X0) | ~ l1_orders_2(X0) | ~ v2_struct_0(X0) ),
% 1.32/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_21,negated_conjecture,
% 1.32/1.00      ( v1_lattice3(sK2) ),
% 1.32/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_311,plain,
% 1.32/1.00      ( ~ l1_orders_2(X0) | ~ v2_struct_0(X0) | sK2 != X0 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_312,plain,
% 1.32/1.00      ( ~ l1_orders_2(sK2) | ~ v2_struct_0(sK2) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_311]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_31,plain,
% 1.32/1.00      ( ~ v1_lattice3(sK2) | ~ l1_orders_2(sK2) | ~ v2_struct_0(sK2) ),
% 1.32/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_314,plain,
% 1.32/1.00      ( ~ v2_struct_0(sK2) ),
% 1.32/1.00      inference(global_propositional_subsumption,
% 1.32/1.00                [status(thm)],
% 1.32/1.00                [c_312,c_21,c_20,c_31]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_324,plain,
% 1.32/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_314]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_325,plain,
% 1.32/1.00      ( ~ l1_struct_0(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_324]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_13,plain,
% 1.32/1.00      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.32/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_37,plain,
% 1.32/1.00      ( ~ l1_orders_2(sK2) | l1_struct_0(sK2) ),
% 1.32/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_50,plain,
% 1.32/1.00      ( v2_struct_0(sK2)
% 1.32/1.00      | ~ l1_struct_0(sK2)
% 1.32/1.00      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.32/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_327,plain,
% 1.32/1.00      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.32/1.00      inference(global_propositional_subsumption,
% 1.32/1.00                [status(thm)],
% 1.32/1.00                [c_325,c_21,c_20,c_31,c_37,c_50]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_375,plain,
% 1.32/1.00      ( r2_hidden(sK0(X0),X0) | u1_struct_0(sK2) != X0 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_327]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_376,plain,
% 1.32/1.00      ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_375]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_377,plain,
% 1.32/1.00      ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2155,plain,
% 1.32/1.00      ( ~ r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2))
% 1.32/1.00      | r2_hidden(k4_tarski(sK0(u1_struct_0(sK2)),sK0(u1_struct_0(sK2))),u1_orders_2(sK2))
% 1.32/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2))
% 1.32/1.00      | ~ v1_relat_1(u1_orders_2(sK2)) ),
% 1.32/1.00      inference(instantiation,[status(thm)],[c_2020]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2156,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) != iProver_top
% 1.32/1.00      | r2_hidden(k4_tarski(sK0(u1_struct_0(sK2)),sK0(u1_struct_0(sK2))),u1_orders_2(sK2)) = iProver_top
% 1.32/1.00      | r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
% 1.32/1.00      | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2155]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2168,plain,
% 1.32/1.00      ( ~ r2_hidden(k4_tarski(sK0(u1_struct_0(sK2)),sK0(u1_struct_0(sK2))),u1_orders_2(sK2))
% 1.32/1.00      | r2_hidden(sK0(u1_orders_2(sK2)),u1_orders_2(sK2)) ),
% 1.32/1.00      inference(instantiation,[status(thm)],[c_1407]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2169,plain,
% 1.32/1.00      ( r2_hidden(k4_tarski(sK0(u1_struct_0(sK2)),sK0(u1_struct_0(sK2))),u1_orders_2(sK2)) != iProver_top
% 1.32/1.00      | r2_hidden(sK0(u1_orders_2(sK2)),u1_orders_2(sK2)) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2168]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2441,plain,
% 1.32/1.00      ( r2_hidden(sK0(u1_orders_2(sK2)),u1_orders_2(sK2)) = iProver_top ),
% 1.32/1.00      inference(global_propositional_subsumption,
% 1.32/1.00                [status(thm)],
% 1.32/1.00                [c_2376,c_23,c_25,c_47,c_377,c_1960,c_1962,c_2156,c_2169]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_4,plain,
% 1.32/1.00      ( r1_relat_2(X0,X1)
% 1.32/1.00      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X0)
% 1.32/1.00      | ~ v1_relat_1(X0) ),
% 1.32/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1411,plain,
% 1.32/1.00      ( r1_relat_2(X0_50,X1_50)
% 1.32/1.00      | ~ r2_hidden(k4_tarski(sK1(X0_50,X1_50),sK1(X0_50,X1_50)),X0_50)
% 1.32/1.00      | ~ v1_relat_1(X0_50) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1841,plain,
% 1.32/1.00      ( r1_relat_2(X0_50,X1_50) = iProver_top
% 1.32/1.00      | r2_hidden(k4_tarski(sK1(X0_50,X1_50),sK1(X0_50,X1_50)),X0_50) != iProver_top
% 1.32/1.00      | v1_relat_1(X0_50) != iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1411]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2241,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(sK2),X0_50) = iProver_top
% 1.32/1.00      | r2_hidden(sK1(u1_orders_2(sK2),X0_50),u1_struct_0(sK2)) != iProver_top
% 1.32/1.00      | v1_relat_1(u1_orders_2(sK2)) != iProver_top ),
% 1.32/1.00      inference(superposition,[status(thm)],[c_2234,c_1841]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2309,plain,
% 1.32/1.00      ( r2_hidden(sK1(u1_orders_2(sK2),X0_50),u1_struct_0(sK2)) != iProver_top
% 1.32/1.00      | r1_relat_2(u1_orders_2(sK2),X0_50) = iProver_top ),
% 1.32/1.00      inference(global_propositional_subsumption,
% 1.32/1.00                [status(thm)],
% 1.32/1.00                [c_2241,c_1960,c_1962]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2310,plain,
% 1.32/1.00      ( r1_relat_2(u1_orders_2(sK2),X0_50) = iProver_top
% 1.32/1.00      | r2_hidden(sK1(u1_orders_2(sK2),X0_50),u1_struct_0(sK2)) != iProver_top ),
% 1.32/1.00      inference(renaming,[status(thm)],[c_2309]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_3,plain,
% 1.32/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.32/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_643,plain,
% 1.32/1.00      ( r2_hidden(X0,X1)
% 1.32/1.00      | v1_xboole_0(X1)
% 1.32/1.00      | u1_orders_2(sK2) != X0
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != X1 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_403]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_644,plain,
% 1.32/1.00      ( r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 1.32/1.00      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_643]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_725,plain,
% 1.32/1.00      ( ~ r2_hidden(X0,X1)
% 1.32/1.00      | r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != X1 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_644]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_726,plain,
% 1.32/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 1.32/1.00      | r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_725]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1397,plain,
% 1.32/1.00      ( ~ r2_hidden(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 1.32/1.00      | r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_726]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1855,plain,
% 1.32/1.00      ( r2_hidden(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 1.32/1.00      | r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1397]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2304,plain,
% 1.32/1.00      ( r1_relat_2(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
% 1.32/1.00      | r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
% 1.32/1.00      | v1_relat_1(X0_50) != iProver_top ),
% 1.32/1.00      inference(superposition,[status(thm)],[c_1842,c_1855]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1854,plain,
% 1.32/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.32/1.00      | v1_relat_1(u1_orders_2(sK2)) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1398]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_2043,plain,
% 1.32/1.00      ( v1_relat_1(u1_orders_2(sK2)) = iProver_top ),
% 1.32/1.00      inference(global_propositional_subsumption,
% 1.32/1.00                [status(thm)],
% 1.32/1.00                [c_1854,c_1960,c_1962]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_737,plain,
% 1.32/1.00      ( r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != u1_struct_0(sK2) ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_327,c_644]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1396,plain,
% 1.32/1.00      ( r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != u1_struct_0(sK2) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_737]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1856,plain,
% 1.32/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) != u1_struct_0(sK2)
% 1.32/1.00      | r2_hidden(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1396]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_19,negated_conjecture,
% 1.32/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.32/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_665,plain,
% 1.32/1.00      ( v1_relat_1(X0)
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != u1_struct_0(sK2)
% 1.32/1.00      | sK3 != X0 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_666,plain,
% 1.32/1.00      ( v1_relat_1(sK3) | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != u1_struct_0(sK2) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_665]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1399,plain,
% 1.32/1.00      ( v1_relat_1(sK3)
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != u1_struct_0(sK2) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_666]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1853,plain,
% 1.32/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != u1_struct_0(sK2)
% 1.32/1.00      | v1_relat_1(sK3) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1399]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_18,negated_conjecture,
% 1.32/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.32/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_653,plain,
% 1.32/1.00      ( v1_relat_1(X0)
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != u1_struct_0(sK2)
% 1.32/1.00      | sK4 != X0 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_654,plain,
% 1.32/1.00      ( v1_relat_1(sK4) | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != u1_struct_0(sK2) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_653]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1400,plain,
% 1.32/1.00      ( v1_relat_1(sK4)
% 1.32/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != u1_struct_0(sK2) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_654]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1852,plain,
% 1.32/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != u1_struct_0(sK2)
% 1.32/1.00      | v1_relat_1(sK4) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1400]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_16,negated_conjecture,
% 1.32/1.00      ( ~ r1_orders_2(sK2,sK4,sK3) | k13_lattice3(sK2,sK3,sK4) != sK3 ),
% 1.32/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_176,plain,
% 1.32/1.00      ( ~ r1_orders_2(sK2,sK4,sK3) | k13_lattice3(sK2,sK3,sK4) != sK3 ),
% 1.32/1.00      inference(prop_impl,[status(thm)],[c_16]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_11,plain,
% 1.32/1.00      ( r1_orders_2(X0,X1,X2)
% 1.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.32/1.00      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 1.32/1.00      | ~ l1_orders_2(X0) ),
% 1.32/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_427,plain,
% 1.32/1.00      ( r1_orders_2(X0,X1,X2)
% 1.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.32/1.00      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 1.32/1.00      | sK2 != X0 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_428,plain,
% 1.32/1.00      ( r1_orders_2(sK2,X0,X1)
% 1.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.32/1.00      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_427]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_588,plain,
% 1.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.32/1.00      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
% 1.32/1.00      | k13_lattice3(sK2,sK3,sK4) != sK3
% 1.32/1.00      | sK3 != X1
% 1.32/1.00      | sK4 != X0
% 1.32/1.00      | sK2 != sK2 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_176,c_428]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_589,plain,
% 1.32/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.32/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.32/1.00      | ~ r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
% 1.32/1.00      | k13_lattice3(sK2,sK3,sK4) != sK3 ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_588]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_591,plain,
% 1.32/1.00      ( ~ r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
% 1.32/1.00      | k13_lattice3(sK2,sK3,sK4) != sK3 ),
% 1.32/1.00      inference(global_propositional_subsumption,
% 1.32/1.00                [status(thm)],
% 1.32/1.00                [c_589,c_19,c_18]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1043,plain,
% 1.32/1.00      ( ~ r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
% 1.32/1.00      | k13_lattice3(sK2,sK3,sK4) != sK3 ),
% 1.32/1.00      inference(prop_impl,[status(thm)],[c_19,c_18,c_589]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1404,plain,
% 1.32/1.00      ( ~ r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
% 1.32/1.00      | k13_lattice3(sK2,sK3,sK4) != sK3 ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_1043]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1848,plain,
% 1.32/1.00      ( k13_lattice3(sK2,sK3,sK4) != sK3
% 1.32/1.00      | r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2)) != iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1404]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_17,negated_conjecture,
% 1.32/1.00      ( r1_orders_2(sK2,sK4,sK3) | k13_lattice3(sK2,sK3,sK4) = sK3 ),
% 1.32/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_178,plain,
% 1.32/1.00      ( r1_orders_2(sK2,sK4,sK3) | k13_lattice3(sK2,sK3,sK4) = sK3 ),
% 1.32/1.00      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_12,plain,
% 1.32/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.32/1.00      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 1.32/1.00      | ~ l1_orders_2(X0) ),
% 1.32/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_409,plain,
% 1.32/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.32/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.32/1.00      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 1.32/1.00      | sK2 != X0 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_410,plain,
% 1.32/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 1.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.32/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.32/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_409]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_574,plain,
% 1.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.32/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
% 1.32/1.00      | k13_lattice3(sK2,sK3,sK4) = sK3
% 1.32/1.00      | sK3 != X1
% 1.32/1.00      | sK4 != X0
% 1.32/1.00      | sK2 != sK2 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_178,c_410]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_575,plain,
% 1.32/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.32/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.32/1.00      | r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
% 1.32/1.00      | k13_lattice3(sK2,sK3,sK4) = sK3 ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_574]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_577,plain,
% 1.32/1.00      ( r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
% 1.32/1.00      | k13_lattice3(sK2,sK3,sK4) = sK3 ),
% 1.32/1.00      inference(global_propositional_subsumption,
% 1.32/1.00                [status(thm)],
% 1.32/1.00                [c_575,c_19,c_18]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1045,plain,
% 1.32/1.00      ( r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
% 1.32/1.00      | k13_lattice3(sK2,sK3,sK4) = sK3 ),
% 1.32/1.00      inference(prop_impl,[status(thm)],[c_19,c_18,c_575]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1405,plain,
% 1.32/1.00      ( r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
% 1.32/1.00      | k13_lattice3(sK2,sK3,sK4) = sK3 ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_1045]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1847,plain,
% 1.32/1.00      ( k13_lattice3(sK2,sK3,sK4) = sK3
% 1.32/1.00      | r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2)) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1405]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_632,plain,
% 1.32/1.00      ( r2_hidden(X0,X1)
% 1.32/1.00      | v1_xboole_0(X1)
% 1.32/1.00      | u1_struct_0(sK2) != X1
% 1.32/1.00      | sK3 != X0 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_19]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_633,plain,
% 1.32/1.00      ( r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_632]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_635,plain,
% 1.32/1.00      ( r2_hidden(sK3,u1_struct_0(sK2)) ),
% 1.32/1.00      inference(global_propositional_subsumption,
% 1.32/1.00                [status(thm)],
% 1.32/1.00                [c_633,c_21,c_20,c_31,c_37,c_50]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1401,plain,
% 1.32/1.00      ( r2_hidden(sK3,u1_struct_0(sK2)) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_635]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1851,plain,
% 1.32/1.00      ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1401]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_621,plain,
% 1.32/1.00      ( r2_hidden(X0,X1)
% 1.32/1.00      | v1_xboole_0(X1)
% 1.32/1.00      | u1_struct_0(sK2) != X1
% 1.32/1.00      | sK4 != X0 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_18]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_622,plain,
% 1.32/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_621]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_624,plain,
% 1.32/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) ),
% 1.32/1.00      inference(global_propositional_subsumption,
% 1.32/1.00                [status(thm)],
% 1.32/1.00                [c_622,c_21,c_20,c_31,c_37,c_50]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1402,plain,
% 1.32/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_624]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1850,plain,
% 1.32/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1402]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_718,plain,
% 1.32/1.00      ( r2_hidden(sK0(X0),X0) | u1_struct_0(sK2) != X0 ),
% 1.32/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_327]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_719,plain,
% 1.32/1.00      ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
% 1.32/1.00      inference(unflattening,[status(thm)],[c_718]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1406,plain,
% 1.32/1.00      ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
% 1.32/1.00      inference(subtyping,[status(esa)],[c_719]) ).
% 1.32/1.00  
% 1.32/1.00  cnf(c_1846,plain,
% 1.32/1.00      ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
% 1.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1406]) ).
% 1.32/1.00  
% 1.32/1.00  
% 1.32/1.00  % SZS output end Saturation for theBenchmark.p
% 1.32/1.00  
% 1.32/1.00  ------                               Statistics
% 1.32/1.00  
% 1.32/1.00  ------ General
% 1.32/1.00  
% 1.32/1.00  abstr_ref_over_cycles:                  0
% 1.32/1.00  abstr_ref_under_cycles:                 0
% 1.32/1.00  gc_basic_clause_elim:                   0
% 1.32/1.00  forced_gc_time:                         0
% 1.32/1.00  parsing_time:                           0.01
% 1.32/1.00  unif_index_cands_time:                  0.
% 1.32/1.00  unif_index_add_time:                    0.
% 1.32/1.00  orderings_time:                         0.
% 1.32/1.00  out_proof_time:                         0.
% 1.32/1.00  total_time:                             0.111
% 1.32/1.00  num_of_symbols:                         56
% 1.32/1.00  num_of_terms:                           1661
% 1.32/1.00  
% 1.32/1.00  ------ Preprocessing
% 1.32/1.00  
% 1.32/1.00  num_of_splits:                          0
% 1.32/1.00  num_of_split_atoms:                     0
% 1.32/1.00  num_of_reused_defs:                     0
% 1.32/1.00  num_eq_ax_congr_red:                    14
% 1.32/1.00  num_of_sem_filtered_clauses:            1
% 1.32/1.00  num_of_subtypes:                        3
% 1.32/1.00  monotx_restored_types:                  0
% 1.32/1.00  sat_num_of_epr_types:                   0
% 1.32/1.00  sat_num_of_non_cyclic_types:            0
% 1.32/1.00  sat_guarded_non_collapsed_types:        0
% 1.32/1.00  num_pure_diseq_elim:                    0
% 1.32/1.00  simp_replaced_by:                       0
% 1.32/1.00  res_preprocessed:                       94
% 1.32/1.00  prep_upred:                             0
% 1.32/1.00  prep_unflattend:                        49
% 1.32/1.00  smt_new_axioms:                         0
% 1.32/1.00  pred_elim_cands:                        3
% 1.32/1.00  pred_elim:                              8
% 1.32/1.00  pred_elim_cl:                           7
% 1.32/1.00  pred_elim_cycles:                       14
% 1.32/1.00  merged_defs:                            8
% 1.32/1.00  merged_defs_ncl:                        0
% 1.32/1.00  bin_hyper_res:                          8
% 1.32/1.00  prep_cycles:                            4
% 1.32/1.00  pred_elim_time:                         0.015
% 1.32/1.00  splitting_time:                         0.
% 1.32/1.00  sem_filter_time:                        0.
% 1.32/1.00  monotx_time:                            0.
% 1.32/1.00  subtype_inf_time:                       0.
% 1.32/1.00  
% 1.32/1.00  ------ Problem properties
% 1.32/1.00  
% 1.32/1.00  clauses:                                16
% 1.32/1.00  conjectures:                            0
% 1.32/1.00  epr:                                    0
% 1.32/1.00  horn:                                   14
% 1.32/1.00  ground:                                 7
% 1.32/1.00  unary:                                  4
% 1.32/1.00  binary:                                 9
% 1.32/1.00  lits:                                   32
% 1.32/1.00  lits_eq:                                6
% 1.32/1.00  fd_pure:                                0
% 1.32/1.00  fd_pseudo:                              0
% 1.32/1.00  fd_cond:                                0
% 1.32/1.00  fd_pseudo_cond:                         0
% 1.32/1.00  ac_symbols:                             0
% 1.32/1.00  
% 1.32/1.00  ------ Propositional Solver
% 1.32/1.00  
% 1.32/1.00  prop_solver_calls:                      28
% 1.32/1.00  prop_fast_solver_calls:                 660
% 1.32/1.00  smt_solver_calls:                       0
% 1.32/1.00  smt_fast_solver_calls:                  0
% 1.32/1.00  prop_num_of_clauses:                    586
% 1.32/1.00  prop_preprocess_simplified:             2985
% 1.32/1.00  prop_fo_subsumed:                       14
% 1.32/1.00  prop_solver_time:                       0.
% 1.32/1.00  smt_solver_time:                        0.
% 1.32/1.00  smt_fast_solver_time:                   0.
% 1.32/1.00  prop_fast_solver_time:                  0.
% 1.32/1.00  prop_unsat_core_time:                   0.
% 1.32/1.00  
% 1.32/1.00  ------ QBF
% 1.32/1.00  
% 1.32/1.00  qbf_q_res:                              0
% 1.32/1.00  qbf_num_tautologies:                    0
% 1.32/1.00  qbf_prep_cycles:                        0
% 1.32/1.00  
% 1.32/1.00  ------ BMC1
% 1.32/1.00  
% 1.32/1.00  bmc1_current_bound:                     -1
% 1.32/1.00  bmc1_last_solved_bound:                 -1
% 1.32/1.00  bmc1_unsat_core_size:                   -1
% 1.32/1.00  bmc1_unsat_core_parents_size:           -1
% 1.32/1.00  bmc1_merge_next_fun:                    0
% 1.32/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.32/1.00  
% 1.32/1.00  ------ Instantiation
% 1.32/1.00  
% 1.32/1.00  inst_num_of_clauses:                    140
% 1.32/1.00  inst_num_in_passive:                    20
% 1.32/1.00  inst_num_in_active:                     119
% 1.32/1.00  inst_num_in_unprocessed:                1
% 1.32/1.00  inst_num_of_loops:                      130
% 1.32/1.00  inst_num_of_learning_restarts:          0
% 1.32/1.00  inst_num_moves_active_passive:          6
% 1.32/1.00  inst_lit_activity:                      0
% 1.32/1.00  inst_lit_activity_moves:                0
% 1.32/1.00  inst_num_tautologies:                   0
% 1.32/1.00  inst_num_prop_implied:                  0
% 1.32/1.00  inst_num_existing_simplified:           0
% 1.32/1.00  inst_num_eq_res_simplified:             0
% 1.32/1.00  inst_num_child_elim:                    0
% 1.32/1.00  inst_num_of_dismatching_blockings:      33
% 1.32/1.00  inst_num_of_non_proper_insts:           151
% 1.32/1.00  inst_num_of_duplicates:                 0
% 1.32/1.00  inst_inst_num_from_inst_to_res:         0
% 1.32/1.00  inst_dismatching_checking_time:         0.
% 1.32/1.00  
% 1.32/1.00  ------ Resolution
% 1.32/1.00  
% 1.32/1.00  res_num_of_clauses:                     0
% 1.32/1.00  res_num_in_passive:                     0
% 1.32/1.00  res_num_in_active:                      0
% 1.32/1.00  res_num_of_loops:                       98
% 1.32/1.00  res_forward_subset_subsumed:            28
% 1.32/1.00  res_backward_subset_subsumed:           0
% 1.32/1.00  res_forward_subsumed:                   0
% 1.32/1.00  res_backward_subsumed:                  0
% 1.32/1.00  res_forward_subsumption_resolution:     0
% 1.32/1.00  res_backward_subsumption_resolution:    0
% 1.32/1.00  res_clause_to_clause_subsumption:       54
% 1.32/1.00  res_orphan_elimination:                 0
% 1.32/1.00  res_tautology_del:                      44
% 1.32/1.00  res_num_eq_res_simplified:              0
% 1.32/1.00  res_num_sel_changes:                    0
% 1.32/1.00  res_moves_from_active_to_pass:          0
% 1.32/1.00  
% 1.32/1.00  ------ Superposition
% 1.32/1.00  
% 1.32/1.00  sup_time_total:                         0.
% 1.32/1.00  sup_time_generating:                    0.
% 1.32/1.00  sup_time_sim_full:                      0.
% 1.32/1.00  sup_time_sim_immed:                     0.
% 1.32/1.00  
% 1.32/1.00  sup_num_of_clauses:                     24
% 1.32/1.00  sup_num_in_active:                      24
% 1.32/1.00  sup_num_in_passive:                     0
% 1.32/1.00  sup_num_of_loops:                       24
% 1.32/1.00  sup_fw_superposition:                   15
% 1.32/1.00  sup_bw_superposition:                   9
% 1.32/1.00  sup_immediate_simplified:               8
% 1.32/1.00  sup_given_eliminated:                   0
% 1.32/1.00  comparisons_done:                       0
% 1.32/1.00  comparisons_avoided:                    0
% 1.32/1.00  
% 1.32/1.00  ------ Simplifications
% 1.32/1.00  
% 1.32/1.00  
% 1.32/1.00  sim_fw_subset_subsumed:                 2
% 1.32/1.00  sim_bw_subset_subsumed:                 0
% 1.32/1.00  sim_fw_subsumed:                        6
% 1.32/1.00  sim_bw_subsumed:                        0
% 1.32/1.00  sim_fw_subsumption_res:                 0
% 1.32/1.00  sim_bw_subsumption_res:                 0
% 1.32/1.00  sim_tautology_del:                      0
% 1.32/1.00  sim_eq_tautology_del:                   0
% 1.32/1.00  sim_eq_res_simp:                        0
% 1.32/1.00  sim_fw_demodulated:                     0
% 1.32/1.00  sim_bw_demodulated:                     0
% 1.32/1.00  sim_light_normalised:                   0
% 1.32/1.00  sim_joinable_taut:                      0
% 1.32/1.00  sim_joinable_simp:                      0
% 1.32/1.00  sim_ac_normalised:                      0
% 1.32/1.00  sim_smt_subsumption:                    0
% 1.32/1.00  
%------------------------------------------------------------------------------
