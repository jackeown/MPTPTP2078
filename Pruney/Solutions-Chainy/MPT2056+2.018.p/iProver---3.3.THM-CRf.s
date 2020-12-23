%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:07 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 470 expanded)
%              Number of clauses        :   74 ( 118 expanded)
%              Number of leaves         :   20 ( 133 expanded)
%              Depth                    :   24
%              Number of atoms          :  471 (2514 expanded)
%              Number of equality atoms :  135 ( 472 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f22])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
     => ( ! [X6,X5,X4,X3,X2] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK2(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5,X6] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK2(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f36])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f32])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) != sK4
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
    & ~ v1_xboole_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f39,f38])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(definition_unfolding,[],[f64,f55])).

fof(f62,plain,(
    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f62,f55])).

fof(f63,plain,(
    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f63,f55])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f57,f55,f55,f55,f55])).

fof(f61,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(definition_unfolding,[],[f61,f55])).

fof(f60,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f56,f55,f55,f55,f55])).

fof(f65,plain,(
    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f46,f45])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_999,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_995,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_991,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_998,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1451,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_998])).

cnf(c_1516,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_1451])).

cnf(c_1830,plain,
    ( k3_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_1516])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_18,negated_conjecture,
    ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_17,negated_conjecture,
    ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_14,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_19,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_237,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_238,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_240,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_238,c_20])).

cnf(c_241,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_240])).

cnf(c_320,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_241])).

cnf(c_365,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_320])).

cnf(c_406,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_365])).

cnf(c_538,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
    inference(equality_resolution_simp,[status(thm)],[c_406])).

cnf(c_699,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_538])).

cnf(c_987,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_2795,plain,
    ( k3_xboole_0(sK4,k1_tarski(X0)) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1830,c_987])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_34,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_36,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_700,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_538])).

cnf(c_733,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_702,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1112,plain,
    ( k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) = k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_715,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1154,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) = u1_struct_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != X0 ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_1236,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) = u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_1237,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) = k3_lattice3(k1_lattice3(k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_698,plain,
    ( v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_538])).

cnf(c_1285,plain,
    ( v1_xboole_0(k2_struct_0(sK3))
    | ~ sP0_iProver_split
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_1286,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1285])).

cnf(c_2904,plain,
    ( v1_xboole_0(X0) != iProver_top
    | k3_xboole_0(sK4,k1_tarski(X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2795,c_23,c_24,c_36,c_733,c_1112,c_1236,c_1237,c_1286])).

cnf(c_2905,plain,
    ( k3_xboole_0(sK4,k1_tarski(X0)) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2904])).

cnf(c_2912,plain,
    ( k3_xboole_0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_999,c_2905])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_397,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_398,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) = k7_subset_1(X1,sK4,X0)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_1128,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
    inference(equality_resolution,[status(thm)],[c_398])).

cnf(c_13,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_285,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_286,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v2_struct_0(sK3)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_22])).

cnf(c_291,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(renaming,[status(thm)],[c_290])).

cnf(c_347,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_291])).

cnf(c_348,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(sK4)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_350,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_348,c_20,c_18,c_16])).

cnf(c_1137,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_1128,c_350])).

cnf(c_15,negated_conjecture,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1158,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) != sK4 ),
    inference(demodulation,[status(thm)],[c_1137,c_15])).

cnf(c_2914,plain,
    ( k5_xboole_0(sK4,k1_xboole_0) != sK4 ),
    inference(demodulation,[status(thm)],[c_2912,c_1158])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_996,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1629,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_996,c_1516])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1259,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_1921,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1629,c_1259])).

cnf(c_2920,plain,
    ( sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_2914,c_1921])).

cnf(c_2921,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2920])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 2.09/1.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.07  
% 2.09/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.09/1.07  
% 2.09/1.07  ------  iProver source info
% 2.09/1.07  
% 2.09/1.07  git: date: 2020-06-30 10:37:57 +0100
% 2.09/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.09/1.07  git: non_committed_changes: false
% 2.09/1.07  git: last_make_outside_of_git: false
% 2.09/1.07  
% 2.09/1.07  ------ 
% 2.09/1.07  
% 2.09/1.07  ------ Input Options
% 2.09/1.07  
% 2.09/1.07  --out_options                           all
% 2.09/1.07  --tptp_safe_out                         true
% 2.09/1.07  --problem_path                          ""
% 2.09/1.07  --include_path                          ""
% 2.09/1.07  --clausifier                            res/vclausify_rel
% 2.09/1.07  --clausifier_options                    --mode clausify
% 2.09/1.07  --stdin                                 false
% 2.09/1.07  --stats_out                             all
% 2.09/1.07  
% 2.09/1.07  ------ General Options
% 2.09/1.07  
% 2.09/1.07  --fof                                   false
% 2.09/1.07  --time_out_real                         305.
% 2.09/1.07  --time_out_virtual                      -1.
% 2.09/1.07  --symbol_type_check                     false
% 2.09/1.07  --clausify_out                          false
% 2.09/1.07  --sig_cnt_out                           false
% 2.09/1.07  --trig_cnt_out                          false
% 2.09/1.07  --trig_cnt_out_tolerance                1.
% 2.09/1.07  --trig_cnt_out_sk_spl                   false
% 2.09/1.07  --abstr_cl_out                          false
% 2.09/1.07  
% 2.09/1.07  ------ Global Options
% 2.09/1.07  
% 2.09/1.07  --schedule                              default
% 2.09/1.07  --add_important_lit                     false
% 2.09/1.07  --prop_solver_per_cl                    1000
% 2.09/1.07  --min_unsat_core                        false
% 2.09/1.07  --soft_assumptions                      false
% 2.09/1.07  --soft_lemma_size                       3
% 2.09/1.07  --prop_impl_unit_size                   0
% 2.09/1.07  --prop_impl_unit                        []
% 2.09/1.07  --share_sel_clauses                     true
% 2.09/1.07  --reset_solvers                         false
% 2.09/1.07  --bc_imp_inh                            [conj_cone]
% 2.09/1.07  --conj_cone_tolerance                   3.
% 2.09/1.07  --extra_neg_conj                        none
% 2.09/1.07  --large_theory_mode                     true
% 2.09/1.07  --prolific_symb_bound                   200
% 2.09/1.07  --lt_threshold                          2000
% 2.09/1.07  --clause_weak_htbl                      true
% 2.09/1.07  --gc_record_bc_elim                     false
% 2.09/1.07  
% 2.09/1.07  ------ Preprocessing Options
% 2.09/1.07  
% 2.09/1.07  --preprocessing_flag                    true
% 2.09/1.07  --time_out_prep_mult                    0.1
% 2.09/1.07  --splitting_mode                        input
% 2.09/1.07  --splitting_grd                         true
% 2.09/1.07  --splitting_cvd                         false
% 2.09/1.07  --splitting_cvd_svl                     false
% 2.09/1.07  --splitting_nvd                         32
% 2.09/1.07  --sub_typing                            true
% 2.09/1.07  --prep_gs_sim                           true
% 2.09/1.07  --prep_unflatten                        true
% 2.09/1.07  --prep_res_sim                          true
% 2.09/1.07  --prep_upred                            true
% 2.09/1.07  --prep_sem_filter                       exhaustive
% 2.09/1.07  --prep_sem_filter_out                   false
% 2.09/1.07  --pred_elim                             true
% 2.09/1.07  --res_sim_input                         true
% 2.09/1.07  --eq_ax_congr_red                       true
% 2.09/1.07  --pure_diseq_elim                       true
% 2.09/1.07  --brand_transform                       false
% 2.09/1.07  --non_eq_to_eq                          false
% 2.09/1.07  --prep_def_merge                        true
% 2.09/1.07  --prep_def_merge_prop_impl              false
% 2.09/1.07  --prep_def_merge_mbd                    true
% 2.09/1.07  --prep_def_merge_tr_red                 false
% 2.09/1.07  --prep_def_merge_tr_cl                  false
% 2.09/1.07  --smt_preprocessing                     true
% 2.09/1.07  --smt_ac_axioms                         fast
% 2.09/1.07  --preprocessed_out                      false
% 2.09/1.07  --preprocessed_stats                    false
% 2.09/1.07  
% 2.09/1.07  ------ Abstraction refinement Options
% 2.09/1.07  
% 2.09/1.07  --abstr_ref                             []
% 2.09/1.07  --abstr_ref_prep                        false
% 2.09/1.07  --abstr_ref_until_sat                   false
% 2.09/1.07  --abstr_ref_sig_restrict                funpre
% 2.09/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/1.07  --abstr_ref_under                       []
% 2.09/1.07  
% 2.09/1.07  ------ SAT Options
% 2.09/1.07  
% 2.09/1.07  --sat_mode                              false
% 2.09/1.07  --sat_fm_restart_options                ""
% 2.09/1.07  --sat_gr_def                            false
% 2.09/1.07  --sat_epr_types                         true
% 2.09/1.07  --sat_non_cyclic_types                  false
% 2.09/1.07  --sat_finite_models                     false
% 2.09/1.07  --sat_fm_lemmas                         false
% 2.09/1.07  --sat_fm_prep                           false
% 2.09/1.07  --sat_fm_uc_incr                        true
% 2.09/1.07  --sat_out_model                         small
% 2.09/1.07  --sat_out_clauses                       false
% 2.09/1.07  
% 2.09/1.07  ------ QBF Options
% 2.09/1.07  
% 2.09/1.07  --qbf_mode                              false
% 2.09/1.07  --qbf_elim_univ                         false
% 2.09/1.07  --qbf_dom_inst                          none
% 2.09/1.07  --qbf_dom_pre_inst                      false
% 2.09/1.07  --qbf_sk_in                             false
% 2.09/1.07  --qbf_pred_elim                         true
% 2.09/1.07  --qbf_split                             512
% 2.09/1.07  
% 2.09/1.07  ------ BMC1 Options
% 2.09/1.07  
% 2.09/1.07  --bmc1_incremental                      false
% 2.09/1.07  --bmc1_axioms                           reachable_all
% 2.09/1.07  --bmc1_min_bound                        0
% 2.09/1.07  --bmc1_max_bound                        -1
% 2.09/1.07  --bmc1_max_bound_default                -1
% 2.09/1.07  --bmc1_symbol_reachability              true
% 2.09/1.07  --bmc1_property_lemmas                  false
% 2.09/1.07  --bmc1_k_induction                      false
% 2.09/1.07  --bmc1_non_equiv_states                 false
% 2.09/1.07  --bmc1_deadlock                         false
% 2.09/1.07  --bmc1_ucm                              false
% 2.09/1.07  --bmc1_add_unsat_core                   none
% 2.09/1.07  --bmc1_unsat_core_children              false
% 2.09/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/1.07  --bmc1_out_stat                         full
% 2.09/1.07  --bmc1_ground_init                      false
% 2.09/1.07  --bmc1_pre_inst_next_state              false
% 2.09/1.07  --bmc1_pre_inst_state                   false
% 2.09/1.07  --bmc1_pre_inst_reach_state             false
% 2.09/1.07  --bmc1_out_unsat_core                   false
% 2.09/1.07  --bmc1_aig_witness_out                  false
% 2.09/1.07  --bmc1_verbose                          false
% 2.09/1.07  --bmc1_dump_clauses_tptp                false
% 2.09/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.09/1.07  --bmc1_dump_file                        -
% 2.09/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.09/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.09/1.07  --bmc1_ucm_extend_mode                  1
% 2.09/1.07  --bmc1_ucm_init_mode                    2
% 2.09/1.07  --bmc1_ucm_cone_mode                    none
% 2.09/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.09/1.07  --bmc1_ucm_relax_model                  4
% 2.09/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.09/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/1.07  --bmc1_ucm_layered_model                none
% 2.09/1.07  --bmc1_ucm_max_lemma_size               10
% 2.09/1.07  
% 2.09/1.07  ------ AIG Options
% 2.09/1.07  
% 2.09/1.07  --aig_mode                              false
% 2.09/1.07  
% 2.09/1.07  ------ Instantiation Options
% 2.09/1.07  
% 2.09/1.07  --instantiation_flag                    true
% 2.09/1.07  --inst_sos_flag                         false
% 2.09/1.07  --inst_sos_phase                        true
% 2.09/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/1.07  --inst_lit_sel_side                     num_symb
% 2.09/1.07  --inst_solver_per_active                1400
% 2.09/1.07  --inst_solver_calls_frac                1.
% 2.09/1.07  --inst_passive_queue_type               priority_queues
% 2.09/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/1.07  --inst_passive_queues_freq              [25;2]
% 2.09/1.07  --inst_dismatching                      true
% 2.09/1.07  --inst_eager_unprocessed_to_passive     true
% 2.09/1.07  --inst_prop_sim_given                   true
% 2.09/1.07  --inst_prop_sim_new                     false
% 2.09/1.07  --inst_subs_new                         false
% 2.09/1.07  --inst_eq_res_simp                      false
% 2.09/1.07  --inst_subs_given                       false
% 2.09/1.07  --inst_orphan_elimination               true
% 2.09/1.07  --inst_learning_loop_flag               true
% 2.09/1.07  --inst_learning_start                   3000
% 2.09/1.07  --inst_learning_factor                  2
% 2.09/1.07  --inst_start_prop_sim_after_learn       3
% 2.09/1.07  --inst_sel_renew                        solver
% 2.09/1.07  --inst_lit_activity_flag                true
% 2.09/1.07  --inst_restr_to_given                   false
% 2.09/1.07  --inst_activity_threshold               500
% 2.09/1.07  --inst_out_proof                        true
% 2.09/1.07  
% 2.09/1.07  ------ Resolution Options
% 2.09/1.07  
% 2.09/1.07  --resolution_flag                       true
% 2.09/1.07  --res_lit_sel                           adaptive
% 2.09/1.07  --res_lit_sel_side                      none
% 2.09/1.07  --res_ordering                          kbo
% 2.09/1.07  --res_to_prop_solver                    active
% 2.09/1.07  --res_prop_simpl_new                    false
% 2.09/1.07  --res_prop_simpl_given                  true
% 2.09/1.07  --res_passive_queue_type                priority_queues
% 2.09/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/1.07  --res_passive_queues_freq               [15;5]
% 2.09/1.07  --res_forward_subs                      full
% 2.09/1.07  --res_backward_subs                     full
% 2.09/1.07  --res_forward_subs_resolution           true
% 2.09/1.07  --res_backward_subs_resolution          true
% 2.09/1.07  --res_orphan_elimination                true
% 2.09/1.07  --res_time_limit                        2.
% 2.09/1.07  --res_out_proof                         true
% 2.09/1.07  
% 2.09/1.07  ------ Superposition Options
% 2.09/1.07  
% 2.09/1.07  --superposition_flag                    true
% 2.09/1.07  --sup_passive_queue_type                priority_queues
% 2.09/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.09/1.07  --demod_completeness_check              fast
% 2.09/1.07  --demod_use_ground                      true
% 2.09/1.07  --sup_to_prop_solver                    passive
% 2.09/1.07  --sup_prop_simpl_new                    true
% 2.09/1.07  --sup_prop_simpl_given                  true
% 2.09/1.07  --sup_fun_splitting                     false
% 2.09/1.07  --sup_smt_interval                      50000
% 2.09/1.07  
% 2.09/1.07  ------ Superposition Simplification Setup
% 2.09/1.07  
% 2.09/1.07  --sup_indices_passive                   []
% 2.09/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/1.07  --sup_full_bw                           [BwDemod]
% 2.09/1.07  --sup_immed_triv                        [TrivRules]
% 2.09/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/1.07  --sup_immed_bw_main                     []
% 2.09/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/1.07  
% 2.09/1.07  ------ Combination Options
% 2.09/1.07  
% 2.09/1.07  --comb_res_mult                         3
% 2.09/1.07  --comb_sup_mult                         2
% 2.09/1.07  --comb_inst_mult                        10
% 2.09/1.07  
% 2.09/1.07  ------ Debug Options
% 2.09/1.07  
% 2.09/1.07  --dbg_backtrace                         false
% 2.09/1.07  --dbg_dump_prop_clauses                 false
% 2.09/1.07  --dbg_dump_prop_clauses_file            -
% 2.09/1.07  --dbg_out_stat                          false
% 2.09/1.07  ------ Parsing...
% 2.09/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.09/1.07  
% 2.09/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.09/1.07  
% 2.09/1.07  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.09/1.07  
% 2.09/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.09/1.07  ------ Proving...
% 2.09/1.07  ------ Problem Properties 
% 2.09/1.07  
% 2.09/1.07  
% 2.09/1.07  clauses                                 19
% 2.09/1.07  conjectures                             2
% 2.09/1.07  EPR                                     5
% 2.09/1.07  Horn                                    12
% 2.09/1.07  unary                                   8
% 2.09/1.07  binary                                  8
% 2.09/1.07  lits                                    39
% 2.09/1.07  lits eq                                 13
% 2.09/1.07  fd_pure                                 0
% 2.09/1.07  fd_pseudo                               0
% 2.09/1.07  fd_cond                                 4
% 2.09/1.07  fd_pseudo_cond                          0
% 2.09/1.07  AC symbols                              0
% 2.09/1.07  
% 2.09/1.07  ------ Schedule dynamic 5 is on 
% 2.09/1.07  
% 2.09/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.09/1.07  
% 2.09/1.07  
% 2.09/1.07  ------ 
% 2.09/1.07  Current options:
% 2.09/1.07  ------ 
% 2.09/1.07  
% 2.09/1.07  ------ Input Options
% 2.09/1.07  
% 2.09/1.07  --out_options                           all
% 2.09/1.07  --tptp_safe_out                         true
% 2.09/1.07  --problem_path                          ""
% 2.09/1.07  --include_path                          ""
% 2.09/1.07  --clausifier                            res/vclausify_rel
% 2.09/1.07  --clausifier_options                    --mode clausify
% 2.09/1.07  --stdin                                 false
% 2.09/1.07  --stats_out                             all
% 2.09/1.07  
% 2.09/1.07  ------ General Options
% 2.09/1.07  
% 2.09/1.07  --fof                                   false
% 2.09/1.07  --time_out_real                         305.
% 2.09/1.07  --time_out_virtual                      -1.
% 2.09/1.07  --symbol_type_check                     false
% 2.09/1.07  --clausify_out                          false
% 2.09/1.07  --sig_cnt_out                           false
% 2.09/1.07  --trig_cnt_out                          false
% 2.09/1.07  --trig_cnt_out_tolerance                1.
% 2.09/1.07  --trig_cnt_out_sk_spl                   false
% 2.09/1.07  --abstr_cl_out                          false
% 2.09/1.07  
% 2.09/1.07  ------ Global Options
% 2.09/1.07  
% 2.09/1.07  --schedule                              default
% 2.09/1.07  --add_important_lit                     false
% 2.09/1.07  --prop_solver_per_cl                    1000
% 2.09/1.07  --min_unsat_core                        false
% 2.09/1.07  --soft_assumptions                      false
% 2.09/1.07  --soft_lemma_size                       3
% 2.09/1.07  --prop_impl_unit_size                   0
% 2.09/1.07  --prop_impl_unit                        []
% 2.09/1.07  --share_sel_clauses                     true
% 2.09/1.07  --reset_solvers                         false
% 2.09/1.07  --bc_imp_inh                            [conj_cone]
% 2.09/1.07  --conj_cone_tolerance                   3.
% 2.09/1.07  --extra_neg_conj                        none
% 2.09/1.07  --large_theory_mode                     true
% 2.09/1.07  --prolific_symb_bound                   200
% 2.09/1.07  --lt_threshold                          2000
% 2.09/1.07  --clause_weak_htbl                      true
% 2.09/1.07  --gc_record_bc_elim                     false
% 2.09/1.07  
% 2.09/1.07  ------ Preprocessing Options
% 2.09/1.07  
% 2.09/1.07  --preprocessing_flag                    true
% 2.09/1.07  --time_out_prep_mult                    0.1
% 2.09/1.07  --splitting_mode                        input
% 2.09/1.07  --splitting_grd                         true
% 2.09/1.07  --splitting_cvd                         false
% 2.09/1.07  --splitting_cvd_svl                     false
% 2.09/1.07  --splitting_nvd                         32
% 2.09/1.07  --sub_typing                            true
% 2.09/1.07  --prep_gs_sim                           true
% 2.09/1.07  --prep_unflatten                        true
% 2.09/1.07  --prep_res_sim                          true
% 2.09/1.07  --prep_upred                            true
% 2.09/1.07  --prep_sem_filter                       exhaustive
% 2.09/1.07  --prep_sem_filter_out                   false
% 2.09/1.07  --pred_elim                             true
% 2.09/1.07  --res_sim_input                         true
% 2.09/1.07  --eq_ax_congr_red                       true
% 2.09/1.07  --pure_diseq_elim                       true
% 2.09/1.07  --brand_transform                       false
% 2.09/1.07  --non_eq_to_eq                          false
% 2.09/1.07  --prep_def_merge                        true
% 2.09/1.07  --prep_def_merge_prop_impl              false
% 2.09/1.07  --prep_def_merge_mbd                    true
% 2.09/1.07  --prep_def_merge_tr_red                 false
% 2.09/1.07  --prep_def_merge_tr_cl                  false
% 2.09/1.07  --smt_preprocessing                     true
% 2.09/1.07  --smt_ac_axioms                         fast
% 2.09/1.07  --preprocessed_out                      false
% 2.09/1.07  --preprocessed_stats                    false
% 2.09/1.07  
% 2.09/1.07  ------ Abstraction refinement Options
% 2.09/1.07  
% 2.09/1.07  --abstr_ref                             []
% 2.09/1.07  --abstr_ref_prep                        false
% 2.09/1.07  --abstr_ref_until_sat                   false
% 2.09/1.07  --abstr_ref_sig_restrict                funpre
% 2.09/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/1.07  --abstr_ref_under                       []
% 2.09/1.07  
% 2.09/1.07  ------ SAT Options
% 2.09/1.07  
% 2.09/1.07  --sat_mode                              false
% 2.09/1.07  --sat_fm_restart_options                ""
% 2.09/1.07  --sat_gr_def                            false
% 2.09/1.07  --sat_epr_types                         true
% 2.09/1.07  --sat_non_cyclic_types                  false
% 2.09/1.07  --sat_finite_models                     false
% 2.09/1.07  --sat_fm_lemmas                         false
% 2.09/1.07  --sat_fm_prep                           false
% 2.09/1.07  --sat_fm_uc_incr                        true
% 2.09/1.07  --sat_out_model                         small
% 2.09/1.07  --sat_out_clauses                       false
% 2.09/1.07  
% 2.09/1.07  ------ QBF Options
% 2.09/1.07  
% 2.09/1.07  --qbf_mode                              false
% 2.09/1.07  --qbf_elim_univ                         false
% 2.09/1.07  --qbf_dom_inst                          none
% 2.09/1.07  --qbf_dom_pre_inst                      false
% 2.09/1.07  --qbf_sk_in                             false
% 2.09/1.07  --qbf_pred_elim                         true
% 2.09/1.07  --qbf_split                             512
% 2.09/1.07  
% 2.09/1.07  ------ BMC1 Options
% 2.09/1.07  
% 2.09/1.07  --bmc1_incremental                      false
% 2.09/1.07  --bmc1_axioms                           reachable_all
% 2.09/1.07  --bmc1_min_bound                        0
% 2.09/1.07  --bmc1_max_bound                        -1
% 2.09/1.07  --bmc1_max_bound_default                -1
% 2.09/1.07  --bmc1_symbol_reachability              true
% 2.09/1.07  --bmc1_property_lemmas                  false
% 2.09/1.07  --bmc1_k_induction                      false
% 2.09/1.07  --bmc1_non_equiv_states                 false
% 2.09/1.07  --bmc1_deadlock                         false
% 2.09/1.07  --bmc1_ucm                              false
% 2.09/1.07  --bmc1_add_unsat_core                   none
% 2.09/1.07  --bmc1_unsat_core_children              false
% 2.09/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/1.07  --bmc1_out_stat                         full
% 2.09/1.07  --bmc1_ground_init                      false
% 2.09/1.07  --bmc1_pre_inst_next_state              false
% 2.09/1.07  --bmc1_pre_inst_state                   false
% 2.09/1.07  --bmc1_pre_inst_reach_state             false
% 2.09/1.07  --bmc1_out_unsat_core                   false
% 2.09/1.07  --bmc1_aig_witness_out                  false
% 2.09/1.07  --bmc1_verbose                          false
% 2.09/1.07  --bmc1_dump_clauses_tptp                false
% 2.09/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.09/1.07  --bmc1_dump_file                        -
% 2.09/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.09/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.09/1.07  --bmc1_ucm_extend_mode                  1
% 2.09/1.07  --bmc1_ucm_init_mode                    2
% 2.09/1.07  --bmc1_ucm_cone_mode                    none
% 2.09/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.09/1.07  --bmc1_ucm_relax_model                  4
% 2.09/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.09/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/1.07  --bmc1_ucm_layered_model                none
% 2.09/1.07  --bmc1_ucm_max_lemma_size               10
% 2.09/1.07  
% 2.09/1.07  ------ AIG Options
% 2.09/1.07  
% 2.09/1.07  --aig_mode                              false
% 2.09/1.07  
% 2.09/1.07  ------ Instantiation Options
% 2.09/1.07  
% 2.09/1.07  --instantiation_flag                    true
% 2.09/1.07  --inst_sos_flag                         false
% 2.09/1.07  --inst_sos_phase                        true
% 2.09/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/1.07  --inst_lit_sel_side                     none
% 2.09/1.07  --inst_solver_per_active                1400
% 2.09/1.07  --inst_solver_calls_frac                1.
% 2.09/1.07  --inst_passive_queue_type               priority_queues
% 2.09/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/1.07  --inst_passive_queues_freq              [25;2]
% 2.09/1.07  --inst_dismatching                      true
% 2.09/1.07  --inst_eager_unprocessed_to_passive     true
% 2.09/1.07  --inst_prop_sim_given                   true
% 2.09/1.07  --inst_prop_sim_new                     false
% 2.09/1.07  --inst_subs_new                         false
% 2.09/1.07  --inst_eq_res_simp                      false
% 2.09/1.07  --inst_subs_given                       false
% 2.09/1.07  --inst_orphan_elimination               true
% 2.09/1.07  --inst_learning_loop_flag               true
% 2.09/1.07  --inst_learning_start                   3000
% 2.09/1.07  --inst_learning_factor                  2
% 2.09/1.07  --inst_start_prop_sim_after_learn       3
% 2.09/1.07  --inst_sel_renew                        solver
% 2.09/1.07  --inst_lit_activity_flag                true
% 2.09/1.07  --inst_restr_to_given                   false
% 2.09/1.07  --inst_activity_threshold               500
% 2.09/1.07  --inst_out_proof                        true
% 2.09/1.07  
% 2.09/1.07  ------ Resolution Options
% 2.09/1.07  
% 2.09/1.07  --resolution_flag                       false
% 2.09/1.07  --res_lit_sel                           adaptive
% 2.09/1.07  --res_lit_sel_side                      none
% 2.09/1.07  --res_ordering                          kbo
% 2.09/1.07  --res_to_prop_solver                    active
% 2.09/1.07  --res_prop_simpl_new                    false
% 2.09/1.07  --res_prop_simpl_given                  true
% 2.09/1.07  --res_passive_queue_type                priority_queues
% 2.09/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/1.07  --res_passive_queues_freq               [15;5]
% 2.09/1.07  --res_forward_subs                      full
% 2.09/1.07  --res_backward_subs                     full
% 2.09/1.07  --res_forward_subs_resolution           true
% 2.09/1.07  --res_backward_subs_resolution          true
% 2.09/1.07  --res_orphan_elimination                true
% 2.09/1.07  --res_time_limit                        2.
% 2.09/1.07  --res_out_proof                         true
% 2.09/1.07  
% 2.09/1.07  ------ Superposition Options
% 2.09/1.07  
% 2.09/1.07  --superposition_flag                    true
% 2.09/1.07  --sup_passive_queue_type                priority_queues
% 2.09/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.09/1.07  --demod_completeness_check              fast
% 2.09/1.07  --demod_use_ground                      true
% 2.09/1.07  --sup_to_prop_solver                    passive
% 2.09/1.07  --sup_prop_simpl_new                    true
% 2.09/1.07  --sup_prop_simpl_given                  true
% 2.09/1.07  --sup_fun_splitting                     false
% 2.09/1.07  --sup_smt_interval                      50000
% 2.09/1.07  
% 2.09/1.07  ------ Superposition Simplification Setup
% 2.09/1.07  
% 2.09/1.07  --sup_indices_passive                   []
% 2.09/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/1.07  --sup_full_bw                           [BwDemod]
% 2.09/1.07  --sup_immed_triv                        [TrivRules]
% 2.09/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/1.07  --sup_immed_bw_main                     []
% 2.09/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/1.07  
% 2.09/1.07  ------ Combination Options
% 2.09/1.07  
% 2.09/1.07  --comb_res_mult                         3
% 2.09/1.07  --comb_sup_mult                         2
% 2.09/1.07  --comb_inst_mult                        10
% 2.09/1.07  
% 2.09/1.07  ------ Debug Options
% 2.09/1.07  
% 2.09/1.07  --dbg_backtrace                         false
% 2.09/1.07  --dbg_dump_prop_clauses                 false
% 2.09/1.07  --dbg_dump_prop_clauses_file            -
% 2.09/1.07  --dbg_out_stat                          false
% 2.09/1.07  
% 2.09/1.07  
% 2.09/1.07  
% 2.09/1.07  
% 2.09/1.07  ------ Proving...
% 2.09/1.07  
% 2.09/1.07  
% 2.09/1.07  % SZS status Theorem for theBenchmark.p
% 2.09/1.07  
% 2.09/1.07   Resolution empty clause
% 2.09/1.07  
% 2.09/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 2.09/1.07  
% 2.09/1.07  fof(f2,axiom,(
% 2.09/1.07    v1_xboole_0(k1_xboole_0)),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f42,plain,(
% 2.09/1.07    v1_xboole_0(k1_xboole_0)),
% 2.09/1.07    inference(cnf_transformation,[],[f2])).
% 2.09/1.07  
% 2.09/1.07  fof(f7,axiom,(
% 2.09/1.07    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f19,plain,(
% 2.09/1.07    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.09/1.07    inference(ennf_transformation,[],[f7])).
% 2.09/1.07  
% 2.09/1.07  fof(f48,plain,(
% 2.09/1.07    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.09/1.07    inference(cnf_transformation,[],[f19])).
% 2.09/1.07  
% 2.09/1.07  fof(f10,axiom,(
% 2.09/1.07    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f22,plain,(
% 2.09/1.07    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.09/1.07    inference(ennf_transformation,[],[f10])).
% 2.09/1.07  
% 2.09/1.07  fof(f23,plain,(
% 2.09/1.07    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.09/1.07    inference(flattening,[],[f22])).
% 2.09/1.07  
% 2.09/1.07  fof(f36,plain,(
% 2.09/1.07    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) => (! [X6,X5,X4,X3,X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK2(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK2(X0),X0)))),
% 2.09/1.07    introduced(choice_axiom,[])).
% 2.09/1.07  
% 2.09/1.07  fof(f37,plain,(
% 2.09/1.07    ! [X0] : ((! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK2(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 2.09/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f36])).
% 2.09/1.07  
% 2.09/1.07  fof(f52,plain,(
% 2.09/1.07    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.09/1.07    inference(cnf_transformation,[],[f37])).
% 2.09/1.07  
% 2.09/1.07  fof(f1,axiom,(
% 2.09/1.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f41,plain,(
% 2.09/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.09/1.07    inference(cnf_transformation,[],[f1])).
% 2.09/1.07  
% 2.09/1.07  fof(f3,axiom,(
% 2.09/1.07    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f17,plain,(
% 2.09/1.07    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.09/1.07    inference(rectify,[],[f3])).
% 2.09/1.07  
% 2.09/1.07  fof(f18,plain,(
% 2.09/1.07    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.09/1.07    inference(ennf_transformation,[],[f17])).
% 2.09/1.07  
% 2.09/1.07  fof(f32,plain,(
% 2.09/1.07    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 2.09/1.07    introduced(choice_axiom,[])).
% 2.09/1.07  
% 2.09/1.07  fof(f33,plain,(
% 2.09/1.07    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.09/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f32])).
% 2.09/1.07  
% 2.09/1.07  fof(f44,plain,(
% 2.09/1.07    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.09/1.07    inference(cnf_transformation,[],[f33])).
% 2.09/1.07  
% 2.09/1.07  fof(f15,conjecture,(
% 2.09/1.07    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f16,negated_conjecture,(
% 2.09/1.07    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.09/1.07    inference(negated_conjecture,[],[f15])).
% 2.09/1.07  
% 2.09/1.07  fof(f30,plain,(
% 2.09/1.07    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 2.09/1.07    inference(ennf_transformation,[],[f16])).
% 2.09/1.07  
% 2.09/1.07  fof(f31,plain,(
% 2.09/1.07    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 2.09/1.07    inference(flattening,[],[f30])).
% 2.09/1.07  
% 2.09/1.07  fof(f39,plain,(
% 2.09/1.07    ( ! [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK4))) )),
% 2.09/1.07    introduced(choice_axiom,[])).
% 2.09/1.07  
% 2.09/1.07  fof(f38,plain,(
% 2.09/1.07    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 2.09/1.07    introduced(choice_axiom,[])).
% 2.09/1.07  
% 2.09/1.07  fof(f40,plain,(
% 2.09/1.07    (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 2.09/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f39,f38])).
% 2.09/1.07  
% 2.09/1.07  fof(f64,plain,(
% 2.09/1.07    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))),
% 2.09/1.07    inference(cnf_transformation,[],[f40])).
% 2.09/1.07  
% 2.09/1.07  fof(f12,axiom,(
% 2.09/1.07    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f55,plain,(
% 2.09/1.07    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.09/1.07    inference(cnf_transformation,[],[f12])).
% 2.09/1.07  
% 2.09/1.07  fof(f70,plain,(
% 2.09/1.07    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))),
% 2.09/1.07    inference(definition_unfolding,[],[f64,f55])).
% 2.09/1.07  
% 2.09/1.07  fof(f62,plain,(
% 2.09/1.07    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 2.09/1.07    inference(cnf_transformation,[],[f40])).
% 2.09/1.07  
% 2.09/1.07  fof(f72,plain,(
% 2.09/1.07    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 2.09/1.07    inference(definition_unfolding,[],[f62,f55])).
% 2.09/1.07  
% 2.09/1.07  fof(f63,plain,(
% 2.09/1.07    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 2.09/1.07    inference(cnf_transformation,[],[f40])).
% 2.09/1.07  
% 2.09/1.07  fof(f71,plain,(
% 2.09/1.07    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 2.09/1.07    inference(definition_unfolding,[],[f63,f55])).
% 2.09/1.07  
% 2.09/1.07  fof(f14,axiom,(
% 2.09/1.07    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f28,plain,(
% 2.09/1.07    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.09/1.07    inference(ennf_transformation,[],[f14])).
% 2.09/1.07  
% 2.09/1.07  fof(f29,plain,(
% 2.09/1.07    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.09/1.07    inference(flattening,[],[f28])).
% 2.09/1.07  
% 2.09/1.07  fof(f57,plain,(
% 2.09/1.07    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.09/1.07    inference(cnf_transformation,[],[f29])).
% 2.09/1.07  
% 2.09/1.07  fof(f69,plain,(
% 2.09/1.07    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.09/1.07    inference(definition_unfolding,[],[f57,f55,f55,f55,f55])).
% 2.09/1.07  
% 2.09/1.07  fof(f61,plain,(
% 2.09/1.07    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))),
% 2.09/1.07    inference(cnf_transformation,[],[f40])).
% 2.09/1.07  
% 2.09/1.07  fof(f73,plain,(
% 2.09/1.07    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))),
% 2.09/1.07    inference(definition_unfolding,[],[f61,f55])).
% 2.09/1.07  
% 2.09/1.07  fof(f60,plain,(
% 2.09/1.07    ~v1_xboole_0(sK4)),
% 2.09/1.07    inference(cnf_transformation,[],[f40])).
% 2.09/1.07  
% 2.09/1.07  fof(f58,plain,(
% 2.09/1.07    ~v2_struct_0(sK3)),
% 2.09/1.07    inference(cnf_transformation,[],[f40])).
% 2.09/1.07  
% 2.09/1.07  fof(f59,plain,(
% 2.09/1.07    l1_struct_0(sK3)),
% 2.09/1.07    inference(cnf_transformation,[],[f40])).
% 2.09/1.07  
% 2.09/1.07  fof(f11,axiom,(
% 2.09/1.07    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f24,plain,(
% 2.09/1.07    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.09/1.07    inference(ennf_transformation,[],[f11])).
% 2.09/1.07  
% 2.09/1.07  fof(f25,plain,(
% 2.09/1.07    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.09/1.07    inference(flattening,[],[f24])).
% 2.09/1.07  
% 2.09/1.07  fof(f54,plain,(
% 2.09/1.07    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.09/1.07    inference(cnf_transformation,[],[f25])).
% 2.09/1.07  
% 2.09/1.07  fof(f8,axiom,(
% 2.09/1.07    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f20,plain,(
% 2.09/1.07    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/1.07    inference(ennf_transformation,[],[f8])).
% 2.09/1.07  
% 2.09/1.07  fof(f49,plain,(
% 2.09/1.07    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/1.07    inference(cnf_transformation,[],[f20])).
% 2.09/1.07  
% 2.09/1.07  fof(f4,axiom,(
% 2.09/1.07    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f45,plain,(
% 2.09/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.09/1.07    inference(cnf_transformation,[],[f4])).
% 2.09/1.07  
% 2.09/1.07  fof(f67,plain,(
% 2.09/1.07    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/1.07    inference(definition_unfolding,[],[f49,f45])).
% 2.09/1.07  
% 2.09/1.07  fof(f13,axiom,(
% 2.09/1.07    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f26,plain,(
% 2.09/1.07    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.09/1.07    inference(ennf_transformation,[],[f13])).
% 2.09/1.07  
% 2.09/1.07  fof(f27,plain,(
% 2.09/1.07    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.09/1.07    inference(flattening,[],[f26])).
% 2.09/1.07  
% 2.09/1.07  fof(f56,plain,(
% 2.09/1.07    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.09/1.07    inference(cnf_transformation,[],[f27])).
% 2.09/1.07  
% 2.09/1.07  fof(f68,plain,(
% 2.09/1.07    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.09/1.07    inference(definition_unfolding,[],[f56,f55,f55,f55,f55])).
% 2.09/1.07  
% 2.09/1.07  fof(f65,plain,(
% 2.09/1.07    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4),
% 2.09/1.07    inference(cnf_transformation,[],[f40])).
% 2.09/1.07  
% 2.09/1.07  fof(f6,axiom,(
% 2.09/1.07    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f47,plain,(
% 2.09/1.07    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.09/1.07    inference(cnf_transformation,[],[f6])).
% 2.09/1.07  
% 2.09/1.07  fof(f5,axiom,(
% 2.09/1.07    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.09/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/1.07  
% 2.09/1.07  fof(f46,plain,(
% 2.09/1.07    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.09/1.07    inference(cnf_transformation,[],[f5])).
% 2.09/1.07  
% 2.09/1.07  fof(f66,plain,(
% 2.09/1.07    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.09/1.07    inference(definition_unfolding,[],[f46,f45])).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1,plain,
% 2.09/1.07      ( v1_xboole_0(k1_xboole_0) ),
% 2.09/1.07      inference(cnf_transformation,[],[f42]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_999,plain,
% 2.09/1.07      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.09/1.07      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_6,plain,
% 2.09/1.07      ( r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1) ),
% 2.09/1.07      inference(cnf_transformation,[],[f48]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_995,plain,
% 2.09/1.07      ( r2_hidden(X0,X1) = iProver_top
% 2.09/1.07      | r1_xboole_0(k1_tarski(X0),X1) = iProver_top ),
% 2.09/1.07      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_11,plain,
% 2.09/1.07      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.09/1.07      inference(cnf_transformation,[],[f52]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_991,plain,
% 2.09/1.07      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 2.09/1.07      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_0,plain,
% 2.09/1.07      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.09/1.07      inference(cnf_transformation,[],[f41]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_2,plain,
% 2.09/1.07      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 2.09/1.07      inference(cnf_transformation,[],[f44]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_998,plain,
% 2.09/1.07      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 2.09/1.07      | r1_xboole_0(X1,X2) != iProver_top ),
% 2.09/1.07      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1451,plain,
% 2.09/1.07      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 2.09/1.07      | r1_xboole_0(X2,X1) != iProver_top ),
% 2.09/1.07      inference(superposition,[status(thm)],[c_0,c_998]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1516,plain,
% 2.09/1.07      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X1,X0) != iProver_top ),
% 2.09/1.07      inference(superposition,[status(thm)],[c_991,c_1451]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1830,plain,
% 2.09/1.07      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0
% 2.09/1.07      | r2_hidden(X1,X0) = iProver_top ),
% 2.09/1.07      inference(superposition,[status(thm)],[c_995,c_1516]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_16,negated_conjecture,
% 2.09/1.07      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
% 2.09/1.07      inference(cnf_transformation,[],[f70]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_18,negated_conjecture,
% 2.09/1.07      ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.09/1.07      inference(cnf_transformation,[],[f72]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_17,negated_conjecture,
% 2.09/1.07      ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.09/1.07      inference(cnf_transformation,[],[f71]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_14,plain,
% 2.09/1.07      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.09/1.07      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.09/1.07      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.09/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.09/1.07      | ~ r2_hidden(X2,X0)
% 2.09/1.07      | ~ v1_xboole_0(X2)
% 2.09/1.07      | v1_xboole_0(X0)
% 2.09/1.07      | v1_xboole_0(X1) ),
% 2.09/1.07      inference(cnf_transformation,[],[f69]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_19,negated_conjecture,
% 2.09/1.07      ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
% 2.09/1.07      inference(cnf_transformation,[],[f73]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_237,plain,
% 2.09/1.07      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.09/1.07      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.09/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.09/1.07      | ~ r2_hidden(X2,X0)
% 2.09/1.07      | ~ v1_xboole_0(X2)
% 2.09/1.07      | v1_xboole_0(X1)
% 2.09/1.07      | v1_xboole_0(X0)
% 2.09/1.07      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.09/1.07      | sK4 != X0 ),
% 2.09/1.07      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_238,plain,
% 2.09/1.07      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.09/1.07      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.09/1.07      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.09/1.07      | ~ r2_hidden(X1,sK4)
% 2.09/1.07      | ~ v1_xboole_0(X1)
% 2.09/1.07      | v1_xboole_0(X0)
% 2.09/1.07      | v1_xboole_0(sK4)
% 2.09/1.07      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.09/1.07      inference(unflattening,[status(thm)],[c_237]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_20,negated_conjecture,
% 2.09/1.07      ( ~ v1_xboole_0(sK4) ),
% 2.09/1.07      inference(cnf_transformation,[],[f60]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_240,plain,
% 2.09/1.07      ( v1_xboole_0(X0)
% 2.09/1.07      | ~ v1_xboole_0(X1)
% 2.09/1.07      | ~ r2_hidden(X1,sK4)
% 2.09/1.07      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.09/1.07      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.09/1.07      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.09/1.07      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.09/1.07      inference(global_propositional_subsumption,[status(thm)],[c_238,c_20]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_241,plain,
% 2.09/1.07      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.09/1.07      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.09/1.07      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.09/1.07      | ~ r2_hidden(X1,sK4)
% 2.09/1.07      | ~ v1_xboole_0(X1)
% 2.09/1.07      | v1_xboole_0(X0)
% 2.09/1.07      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.09/1.07      inference(renaming,[status(thm)],[c_240]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_320,plain,
% 2.09/1.07      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.09/1.07      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.09/1.07      | ~ r2_hidden(X1,sK4)
% 2.09/1.07      | ~ v1_xboole_0(X1)
% 2.09/1.07      | v1_xboole_0(X0)
% 2.09/1.07      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.09/1.07      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.09/1.07      | sK4 != sK4 ),
% 2.09/1.07      inference(resolution_lifted,[status(thm)],[c_17,c_241]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_365,plain,
% 2.09/1.07      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.09/1.07      | ~ r2_hidden(X1,sK4)
% 2.09/1.07      | ~ v1_xboole_0(X1)
% 2.09/1.07      | v1_xboole_0(X0)
% 2.09/1.07      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.09/1.07      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.09/1.07      | sK4 != sK4 ),
% 2.09/1.07      inference(resolution_lifted,[status(thm)],[c_18,c_320]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_406,plain,
% 2.09/1.07      ( ~ r2_hidden(X0,sK4)
% 2.09/1.07      | ~ v1_xboole_0(X0)
% 2.09/1.07      | v1_xboole_0(X1)
% 2.09/1.07      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.09/1.07      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.09/1.07      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.09/1.07      | sK4 != sK4 ),
% 2.09/1.07      inference(resolution_lifted,[status(thm)],[c_16,c_365]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_538,plain,
% 2.09/1.07      ( ~ r2_hidden(X0,sK4)
% 2.09/1.07      | ~ v1_xboole_0(X0)
% 2.09/1.07      | v1_xboole_0(X1)
% 2.09/1.07      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.09/1.07      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.09/1.07      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
% 2.09/1.07      inference(equality_resolution_simp,[status(thm)],[c_406]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_699,plain,
% 2.09/1.07      ( ~ r2_hidden(X0,sK4) | ~ v1_xboole_0(X0) | ~ sP1_iProver_split ),
% 2.09/1.07      inference(splitting,
% 2.09/1.07                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.09/1.07                [c_538]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_987,plain,
% 2.09/1.07      ( r2_hidden(X0,sK4) != iProver_top
% 2.09/1.07      | v1_xboole_0(X0) != iProver_top
% 2.09/1.07      | sP1_iProver_split != iProver_top ),
% 2.09/1.07      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_2795,plain,
% 2.09/1.07      ( k3_xboole_0(sK4,k1_tarski(X0)) = k1_xboole_0
% 2.09/1.07      | v1_xboole_0(X0) != iProver_top
% 2.09/1.07      | sP1_iProver_split != iProver_top ),
% 2.09/1.07      inference(superposition,[status(thm)],[c_1830,c_987]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_22,negated_conjecture,
% 2.09/1.07      ( ~ v2_struct_0(sK3) ),
% 2.09/1.07      inference(cnf_transformation,[],[f58]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_23,plain,
% 2.09/1.07      ( v2_struct_0(sK3) != iProver_top ),
% 2.09/1.07      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_21,negated_conjecture,
% 2.09/1.07      ( l1_struct_0(sK3) ),
% 2.09/1.07      inference(cnf_transformation,[],[f59]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_24,plain,
% 2.09/1.07      ( l1_struct_0(sK3) = iProver_top ),
% 2.09/1.07      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_12,plain,
% 2.09/1.07      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.09/1.07      inference(cnf_transformation,[],[f54]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_34,plain,
% 2.09/1.07      ( v2_struct_0(X0) = iProver_top
% 2.09/1.07      | l1_struct_0(X0) != iProver_top
% 2.09/1.07      | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
% 2.09/1.07      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_36,plain,
% 2.09/1.07      ( v2_struct_0(sK3) = iProver_top
% 2.09/1.07      | l1_struct_0(sK3) != iProver_top
% 2.09/1.07      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 2.09/1.07      inference(instantiation,[status(thm)],[c_34]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_700,plain,
% 2.09/1.07      ( sP1_iProver_split | sP0_iProver_split ),
% 2.09/1.07      inference(splitting,
% 2.09/1.07                [splitting(split),new_symbols(definition,[])],
% 2.09/1.07                [c_538]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_733,plain,
% 2.09/1.07      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.09/1.07      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_702,plain,( X0 = X0 ),theory(equality) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1112,plain,
% 2.09/1.07      ( k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) = k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
% 2.09/1.07      inference(instantiation,[status(thm)],[c_702]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_715,plain,
% 2.09/1.07      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 2.09/1.07      theory(equality) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1154,plain,
% 2.09/1.07      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) = u1_struct_0(X0)
% 2.09/1.07      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != X0 ),
% 2.09/1.07      inference(instantiation,[status(thm)],[c_715]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1236,plain,
% 2.09/1.07      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) = u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.09/1.07      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3))) ),
% 2.09/1.07      inference(instantiation,[status(thm)],[c_1154]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1237,plain,
% 2.09/1.07      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) = k3_lattice3(k1_lattice3(k2_struct_0(sK3))) ),
% 2.09/1.07      inference(instantiation,[status(thm)],[c_702]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_698,plain,
% 2.09/1.07      ( v1_xboole_0(X0)
% 2.09/1.07      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.09/1.07      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.09/1.07      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 2.09/1.07      | ~ sP0_iProver_split ),
% 2.09/1.07      inference(splitting,
% 2.09/1.07                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.09/1.07                [c_538]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1285,plain,
% 2.09/1.07      ( v1_xboole_0(k2_struct_0(sK3))
% 2.09/1.07      | ~ sP0_iProver_split
% 2.09/1.07      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.09/1.07      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 2.09/1.07      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
% 2.09/1.07      inference(instantiation,[status(thm)],[c_698]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1286,plain,
% 2.09/1.07      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.09/1.07      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 2.09/1.07      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))
% 2.09/1.07      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 2.09/1.07      | sP0_iProver_split != iProver_top ),
% 2.09/1.07      inference(predicate_to_equality,[status(thm)],[c_1285]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_2904,plain,
% 2.09/1.07      ( v1_xboole_0(X0) != iProver_top
% 2.09/1.07      | k3_xboole_0(sK4,k1_tarski(X0)) = k1_xboole_0 ),
% 2.09/1.07      inference(global_propositional_subsumption,
% 2.09/1.07                [status(thm)],
% 2.09/1.07                [c_2795,c_23,c_24,c_36,c_733,c_1112,c_1236,c_1237,c_1286]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_2905,plain,
% 2.09/1.07      ( k3_xboole_0(sK4,k1_tarski(X0)) = k1_xboole_0
% 2.09/1.07      | v1_xboole_0(X0) != iProver_top ),
% 2.09/1.07      inference(renaming,[status(thm)],[c_2904]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_2912,plain,
% 2.09/1.07      ( k3_xboole_0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
% 2.09/1.07      inference(superposition,[status(thm)],[c_999,c_2905]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_7,plain,
% 2.09/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.09/1.07      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 2.09/1.07      inference(cnf_transformation,[],[f67]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_397,plain,
% 2.09/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 2.09/1.07      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X2)
% 2.09/1.07      | sK4 != X0 ),
% 2.09/1.07      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_398,plain,
% 2.09/1.07      ( k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) = k7_subset_1(X1,sK4,X0)
% 2.09/1.07      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X1) ),
% 2.09/1.07      inference(unflattening,[status(thm)],[c_397]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1128,plain,
% 2.09/1.07      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
% 2.09/1.07      inference(equality_resolution,[status(thm)],[c_398]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_13,plain,
% 2.09/1.07      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.09/1.07      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.09/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.09/1.07      | v2_struct_0(X1)
% 2.09/1.07      | ~ l1_struct_0(X1)
% 2.09/1.07      | v1_xboole_0(X0)
% 2.09/1.07      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
% 2.09/1.07      inference(cnf_transformation,[],[f68]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_285,plain,
% 2.09/1.07      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.09/1.07      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.09/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.09/1.07      | v2_struct_0(X1)
% 2.09/1.07      | v1_xboole_0(X0)
% 2.09/1.07      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
% 2.09/1.07      | sK3 != X1 ),
% 2.09/1.07      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_286,plain,
% 2.09/1.07      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.09/1.07      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.09/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.09/1.07      | v2_struct_0(sK3)
% 2.09/1.07      | v1_xboole_0(X0)
% 2.09/1.07      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 2.09/1.07      inference(unflattening,[status(thm)],[c_285]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_290,plain,
% 2.09/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.09/1.07      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.09/1.07      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.09/1.07      | v1_xboole_0(X0)
% 2.09/1.07      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 2.09/1.07      inference(global_propositional_subsumption,[status(thm)],[c_286,c_22]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_291,plain,
% 2.09/1.07      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.09/1.07      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.09/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.09/1.07      | v1_xboole_0(X0)
% 2.09/1.07      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 2.09/1.07      inference(renaming,[status(thm)],[c_290]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_347,plain,
% 2.09/1.07      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.09/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.09/1.07      | v1_xboole_0(X0)
% 2.09/1.07      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
% 2.09/1.07      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 2.09/1.07      | sK4 != X0 ),
% 2.09/1.07      inference(resolution_lifted,[status(thm)],[c_17,c_291]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_348,plain,
% 2.09/1.07      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.09/1.07      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.09/1.07      | v1_xboole_0(sK4)
% 2.09/1.07      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.09/1.07      inference(unflattening,[status(thm)],[c_347]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_350,plain,
% 2.09/1.07      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.09/1.07      inference(global_propositional_subsumption,
% 2.09/1.07                [status(thm)],
% 2.09/1.07                [c_348,c_20,c_18,c_16]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1137,plain,
% 2.09/1.07      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) ),
% 2.09/1.07      inference(demodulation,[status(thm)],[c_1128,c_350]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_15,negated_conjecture,
% 2.09/1.07      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
% 2.09/1.07      inference(cnf_transformation,[],[f65]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1158,plain,
% 2.09/1.07      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) != sK4 ),
% 2.09/1.07      inference(demodulation,[status(thm)],[c_1137,c_15]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_2914,plain,
% 2.09/1.07      ( k5_xboole_0(sK4,k1_xboole_0) != sK4 ),
% 2.09/1.07      inference(demodulation,[status(thm)],[c_2912,c_1158]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_5,plain,
% 2.09/1.07      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.09/1.07      inference(cnf_transformation,[],[f47]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_996,plain,
% 2.09/1.07      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.09/1.07      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1629,plain,
% 2.09/1.07      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.09/1.07      inference(superposition,[status(thm)],[c_996,c_1516]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_4,plain,
% 2.09/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 2.09/1.07      inference(cnf_transformation,[],[f66]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1259,plain,
% 2.09/1.07      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 2.09/1.07      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_1921,plain,
% 2.09/1.07      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.09/1.07      inference(demodulation,[status(thm)],[c_1629,c_1259]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_2920,plain,
% 2.09/1.07      ( sK4 != sK4 ),
% 2.09/1.07      inference(demodulation,[status(thm)],[c_2914,c_1921]) ).
% 2.09/1.07  
% 2.09/1.07  cnf(c_2921,plain,
% 2.09/1.07      ( $false ),
% 2.09/1.07      inference(equality_resolution_simp,[status(thm)],[c_2920]) ).
% 2.09/1.07  
% 2.09/1.07  
% 2.09/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 2.09/1.07  
% 2.09/1.07  ------                               Statistics
% 2.09/1.07  
% 2.09/1.07  ------ General
% 2.09/1.07  
% 2.09/1.07  abstr_ref_over_cycles:                  0
% 2.09/1.07  abstr_ref_under_cycles:                 0
% 2.09/1.07  gc_basic_clause_elim:                   0
% 2.09/1.07  forced_gc_time:                         0
% 2.09/1.07  parsing_time:                           0.01
% 2.09/1.07  unif_index_cands_time:                  0.
% 2.09/1.07  unif_index_add_time:                    0.
% 2.09/1.07  orderings_time:                         0.
% 2.09/1.07  out_proof_time:                         0.016
% 2.09/1.07  total_time:                             0.181
% 2.09/1.07  num_of_symbols:                         59
% 2.09/1.07  num_of_terms:                           3349
% 2.09/1.07  
% 2.09/1.07  ------ Preprocessing
% 2.09/1.07  
% 2.09/1.07  num_of_splits:                          2
% 2.09/1.07  num_of_split_atoms:                     2
% 2.09/1.07  num_of_reused_defs:                     0
% 2.09/1.07  num_eq_ax_congr_red:                    15
% 2.09/1.07  num_of_sem_filtered_clauses:            1
% 2.09/1.07  num_of_subtypes:                        0
% 2.09/1.07  monotx_restored_types:                  0
% 2.09/1.07  sat_num_of_epr_types:                   0
% 2.09/1.07  sat_num_of_non_cyclic_types:            0
% 2.09/1.07  sat_guarded_non_collapsed_types:        0
% 2.09/1.07  num_pure_diseq_elim:                    0
% 2.09/1.07  simp_replaced_by:                       0
% 2.09/1.07  res_preprocessed:                       111
% 2.09/1.07  prep_upred:                             0
% 2.09/1.07  prep_unflattend:                        25
% 2.09/1.07  smt_new_axioms:                         0
% 2.09/1.07  pred_elim_cands:                        3
% 2.09/1.07  pred_elim:                              6
% 2.09/1.07  pred_elim_cl:                           6
% 2.09/1.07  pred_elim_cycles:                       8
% 2.09/1.07  merged_defs:                            0
% 2.09/1.07  merged_defs_ncl:                        0
% 2.09/1.07  bin_hyper_res:                          0
% 2.09/1.07  prep_cycles:                            4
% 2.09/1.07  pred_elim_time:                         0.008
% 2.09/1.07  splitting_time:                         0.
% 2.09/1.07  sem_filter_time:                        0.
% 2.09/1.07  monotx_time:                            0.
% 2.09/1.07  subtype_inf_time:                       0.
% 2.09/1.07  
% 2.09/1.07  ------ Problem properties
% 2.09/1.07  
% 2.09/1.07  clauses:                                19
% 2.09/1.07  conjectures:                            2
% 2.09/1.07  epr:                                    5
% 2.09/1.07  horn:                                   12
% 2.09/1.07  ground:                                 6
% 2.09/1.07  unary:                                  8
% 2.09/1.07  binary:                                 8
% 2.09/1.07  lits:                                   39
% 2.09/1.07  lits_eq:                                13
% 2.09/1.07  fd_pure:                                0
% 2.09/1.07  fd_pseudo:                              0
% 2.09/1.07  fd_cond:                                4
% 2.09/1.07  fd_pseudo_cond:                         0
% 2.09/1.07  ac_symbols:                             0
% 2.09/1.07  
% 2.09/1.07  ------ Propositional Solver
% 2.09/1.07  
% 2.09/1.07  prop_solver_calls:                      29
% 2.09/1.07  prop_fast_solver_calls:                 696
% 2.09/1.07  smt_solver_calls:                       0
% 2.09/1.07  smt_fast_solver_calls:                  0
% 2.09/1.07  prop_num_of_clauses:                    1098
% 2.09/1.07  prop_preprocess_simplified:             3738
% 2.09/1.07  prop_fo_subsumed:                       16
% 2.09/1.07  prop_solver_time:                       0.
% 2.09/1.07  smt_solver_time:                        0.
% 2.09/1.07  smt_fast_solver_time:                   0.
% 2.09/1.07  prop_fast_solver_time:                  0.
% 2.09/1.07  prop_unsat_core_time:                   0.
% 2.09/1.07  
% 2.09/1.07  ------ QBF
% 2.09/1.07  
% 2.09/1.07  qbf_q_res:                              0
% 2.09/1.07  qbf_num_tautologies:                    0
% 2.09/1.07  qbf_prep_cycles:                        0
% 2.09/1.07  
% 2.09/1.07  ------ BMC1
% 2.09/1.07  
% 2.09/1.07  bmc1_current_bound:                     -1
% 2.09/1.07  bmc1_last_solved_bound:                 -1
% 2.09/1.07  bmc1_unsat_core_size:                   -1
% 2.09/1.07  bmc1_unsat_core_parents_size:           -1
% 2.09/1.07  bmc1_merge_next_fun:                    0
% 2.09/1.07  bmc1_unsat_core_clauses_time:           0.
% 2.09/1.07  
% 2.09/1.07  ------ Instantiation
% 2.09/1.07  
% 2.09/1.07  inst_num_of_clauses:                    386
% 2.09/1.07  inst_num_in_passive:                    119
% 2.09/1.07  inst_num_in_active:                     176
% 2.09/1.07  inst_num_in_unprocessed:                91
% 2.09/1.07  inst_num_of_loops:                      210
% 2.09/1.07  inst_num_of_learning_restarts:          0
% 2.09/1.07  inst_num_moves_active_passive:          30
% 2.09/1.07  inst_lit_activity:                      0
% 2.09/1.07  inst_lit_activity_moves:                0
% 2.09/1.07  inst_num_tautologies:                   0
% 2.09/1.07  inst_num_prop_implied:                  0
% 2.09/1.07  inst_num_existing_simplified:           0
% 2.09/1.07  inst_num_eq_res_simplified:             0
% 2.09/1.07  inst_num_child_elim:                    0
% 2.09/1.07  inst_num_of_dismatching_blockings:      34
% 2.09/1.07  inst_num_of_non_proper_insts:           276
% 2.09/1.07  inst_num_of_duplicates:                 0
% 2.09/1.07  inst_inst_num_from_inst_to_res:         0
% 2.09/1.07  inst_dismatching_checking_time:         0.
% 2.09/1.07  
% 2.09/1.07  ------ Resolution
% 2.09/1.07  
% 2.09/1.07  res_num_of_clauses:                     0
% 2.09/1.07  res_num_in_passive:                     0
% 2.09/1.07  res_num_in_active:                      0
% 2.09/1.07  res_num_of_loops:                       115
% 2.09/1.07  res_forward_subset_subsumed:            52
% 2.09/1.07  res_backward_subset_subsumed:           4
% 2.09/1.07  res_forward_subsumed:                   0
% 2.09/1.07  res_backward_subsumed:                  0
% 2.09/1.07  res_forward_subsumption_resolution:     0
% 2.09/1.07  res_backward_subsumption_resolution:    0
% 2.09/1.07  res_clause_to_clause_subsumption:       137
% 2.09/1.07  res_orphan_elimination:                 0
% 2.09/1.07  res_tautology_del:                      28
% 2.09/1.07  res_num_eq_res_simplified:              1
% 2.09/1.07  res_num_sel_changes:                    0
% 2.09/1.07  res_moves_from_active_to_pass:          0
% 2.09/1.07  
% 2.09/1.07  ------ Superposition
% 2.09/1.07  
% 2.09/1.07  sup_time_total:                         0.
% 2.09/1.07  sup_time_generating:                    0.
% 2.09/1.07  sup_time_sim_full:                      0.
% 2.09/1.07  sup_time_sim_immed:                     0.
% 2.09/1.07  
% 2.09/1.07  sup_num_of_clauses:                     49
% 2.09/1.07  sup_num_in_active:                      35
% 2.09/1.07  sup_num_in_passive:                     14
% 2.09/1.07  sup_num_of_loops:                       41
% 2.09/1.07  sup_fw_superposition:                   33
% 2.09/1.07  sup_bw_superposition:                   46
% 2.09/1.07  sup_immediate_simplified:               3
% 2.09/1.07  sup_given_eliminated:                   0
% 2.09/1.07  comparisons_done:                       0
% 2.09/1.07  comparisons_avoided:                    0
% 2.09/1.07  
% 2.09/1.07  ------ Simplifications
% 2.09/1.07  
% 2.09/1.07  
% 2.09/1.07  sim_fw_subset_subsumed:                 1
% 2.09/1.07  sim_bw_subset_subsumed:                 1
% 2.09/1.07  sim_fw_subsumed:                        4
% 2.09/1.07  sim_bw_subsumed:                        0
% 2.09/1.07  sim_fw_subsumption_res:                 1
% 2.09/1.07  sim_bw_subsumption_res:                 0
% 2.09/1.07  sim_tautology_del:                      2
% 2.09/1.07  sim_eq_tautology_del:                   1
% 2.09/1.07  sim_eq_res_simp:                        0
% 2.09/1.07  sim_fw_demodulated:                     2
% 2.09/1.07  sim_bw_demodulated:                     6
% 2.09/1.07  sim_light_normalised:                   0
% 2.09/1.07  sim_joinable_taut:                      0
% 2.09/1.07  sim_joinable_simp:                      0
% 2.09/1.07  sim_ac_normalised:                      0
% 2.09/1.07  sim_smt_subsumption:                    0
% 2.09/1.07  
%------------------------------------------------------------------------------
