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
% DateTime   : Thu Dec  3 12:29:06 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 459 expanded)
%              Number of clauses        :   70 ( 106 expanded)
%              Number of leaves         :   20 ( 130 expanded)
%              Depth                    :   25
%              Number of atoms          :  475 (2503 expanded)
%              Number of equality atoms :  135 ( 462 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f40])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f38])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
    & ~ v1_xboole_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f43,f42])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(definition_unfolding,[],[f70,f61])).

fof(f68,plain,(
    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f68,f61])).

fof(f69,plain,(
    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f69,f61])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f63,f61,f61,f61,f61])).

fof(f67,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(definition_unfolding,[],[f67,f61])).

fof(f66,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f51])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f62,f61,f61,f61,f61])).

fof(f71,plain,(
    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f54,f51])).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f52,f72])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f53,f51])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_929,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_926,plain,
    ( r1_xboole_0(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_924,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_928,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1500,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_928])).

cnf(c_1675,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_924,c_1500])).

cnf(c_2006,plain,
    ( k3_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_1675])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_19,negated_conjecture,
    ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_18,negated_conjecture,
    ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_15,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_20,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_238,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_239,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_241,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_239,c_21])).

cnf(c_242,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_241])).

cnf(c_323,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_242])).

cnf(c_368,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_323])).

cnf(c_409,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_368])).

cnf(c_514,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
    inference(equality_resolution_simp,[status(thm)],[c_409])).

cnf(c_648,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_514])).

cnf(c_920,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_2570,plain,
    ( k3_xboole_0(sK4,k1_tarski(X0)) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2006,c_920])).

cnf(c_649,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_514])).

cnf(c_682,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_275,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_276,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_278,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_276,c_22])).

cnf(c_922,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_12,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_317,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_318,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_938,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_922,c_318])).

cnf(c_647,plain,
    ( v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_514])).

cnf(c_921,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_1398,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_921])).

cnf(c_1450,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1398])).

cnf(c_2688,plain,
    ( v1_xboole_0(X0) != iProver_top
    | k3_xboole_0(sK4,k1_tarski(X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2570,c_682,c_938,c_1450])).

cnf(c_2689,plain,
    ( k3_xboole_0(sK4,k1_tarski(X0)) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2688])).

cnf(c_2696,plain,
    ( k3_xboole_0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_929,c_2689])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_400,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_401,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) = k7_subset_1(X1,sK4,X0)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_1076,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
    inference(equality_resolution,[status(thm)],[c_401])).

cnf(c_14,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_286,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_287,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | ~ l1_struct_0(sK3)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_287,c_22])).

cnf(c_290,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(renaming,[status(thm)],[c_289])).

cnf(c_350,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_290])).

cnf(c_351,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(sK4)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_353,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_351,c_21,c_19,c_17])).

cnf(c_1094,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_1076,c_353])).

cnf(c_16,negated_conjecture,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1096,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) != sK4 ),
    inference(demodulation,[status(thm)],[c_1094,c_16])).

cnf(c_2810,plain,
    ( k5_xboole_0(sK4,k1_xboole_0) != sK4 ),
    inference(demodulation,[status(thm)],[c_2696,c_1096])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_949,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_7])).

cnf(c_2816,plain,
    ( sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_2810,c_949])).

cnf(c_2817,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2816])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.00/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/0.99  
% 2.00/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.00/0.99  
% 2.00/0.99  ------  iProver source info
% 2.00/0.99  
% 2.00/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.00/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.00/0.99  git: non_committed_changes: false
% 2.00/0.99  git: last_make_outside_of_git: false
% 2.00/0.99  
% 2.00/0.99  ------ 
% 2.00/0.99  
% 2.00/0.99  ------ Input Options
% 2.00/0.99  
% 2.00/0.99  --out_options                           all
% 2.00/0.99  --tptp_safe_out                         true
% 2.00/0.99  --problem_path                          ""
% 2.00/0.99  --include_path                          ""
% 2.00/0.99  --clausifier                            res/vclausify_rel
% 2.00/0.99  --clausifier_options                    --mode clausify
% 2.00/0.99  --stdin                                 false
% 2.00/0.99  --stats_out                             all
% 2.00/0.99  
% 2.00/0.99  ------ General Options
% 2.00/0.99  
% 2.00/0.99  --fof                                   false
% 2.00/0.99  --time_out_real                         305.
% 2.00/0.99  --time_out_virtual                      -1.
% 2.00/0.99  --symbol_type_check                     false
% 2.00/0.99  --clausify_out                          false
% 2.00/0.99  --sig_cnt_out                           false
% 2.00/0.99  --trig_cnt_out                          false
% 2.00/0.99  --trig_cnt_out_tolerance                1.
% 2.00/0.99  --trig_cnt_out_sk_spl                   false
% 2.00/0.99  --abstr_cl_out                          false
% 2.00/0.99  
% 2.00/0.99  ------ Global Options
% 2.00/0.99  
% 2.00/0.99  --schedule                              default
% 2.00/0.99  --add_important_lit                     false
% 2.00/0.99  --prop_solver_per_cl                    1000
% 2.00/0.99  --min_unsat_core                        false
% 2.00/0.99  --soft_assumptions                      false
% 2.00/0.99  --soft_lemma_size                       3
% 2.00/0.99  --prop_impl_unit_size                   0
% 2.00/0.99  --prop_impl_unit                        []
% 2.00/0.99  --share_sel_clauses                     true
% 2.00/0.99  --reset_solvers                         false
% 2.00/0.99  --bc_imp_inh                            [conj_cone]
% 2.00/0.99  --conj_cone_tolerance                   3.
% 2.00/0.99  --extra_neg_conj                        none
% 2.00/0.99  --large_theory_mode                     true
% 2.00/0.99  --prolific_symb_bound                   200
% 2.00/0.99  --lt_threshold                          2000
% 2.00/0.99  --clause_weak_htbl                      true
% 2.00/0.99  --gc_record_bc_elim                     false
% 2.00/0.99  
% 2.00/0.99  ------ Preprocessing Options
% 2.00/0.99  
% 2.00/0.99  --preprocessing_flag                    true
% 2.00/0.99  --time_out_prep_mult                    0.1
% 2.00/0.99  --splitting_mode                        input
% 2.00/0.99  --splitting_grd                         true
% 2.00/0.99  --splitting_cvd                         false
% 2.00/0.99  --splitting_cvd_svl                     false
% 2.00/0.99  --splitting_nvd                         32
% 2.00/0.99  --sub_typing                            true
% 2.00/0.99  --prep_gs_sim                           true
% 2.00/0.99  --prep_unflatten                        true
% 2.00/0.99  --prep_res_sim                          true
% 2.00/0.99  --prep_upred                            true
% 2.00/0.99  --prep_sem_filter                       exhaustive
% 2.00/0.99  --prep_sem_filter_out                   false
% 2.00/0.99  --pred_elim                             true
% 2.00/0.99  --res_sim_input                         true
% 2.00/0.99  --eq_ax_congr_red                       true
% 2.00/0.99  --pure_diseq_elim                       true
% 2.00/0.99  --brand_transform                       false
% 2.00/0.99  --non_eq_to_eq                          false
% 2.00/0.99  --prep_def_merge                        true
% 2.00/0.99  --prep_def_merge_prop_impl              false
% 2.00/1.00  --prep_def_merge_mbd                    true
% 2.00/1.00  --prep_def_merge_tr_red                 false
% 2.00/1.00  --prep_def_merge_tr_cl                  false
% 2.00/1.00  --smt_preprocessing                     true
% 2.00/1.00  --smt_ac_axioms                         fast
% 2.00/1.00  --preprocessed_out                      false
% 2.00/1.00  --preprocessed_stats                    false
% 2.00/1.00  
% 2.00/1.00  ------ Abstraction refinement Options
% 2.00/1.00  
% 2.00/1.00  --abstr_ref                             []
% 2.00/1.00  --abstr_ref_prep                        false
% 2.00/1.00  --abstr_ref_until_sat                   false
% 2.00/1.00  --abstr_ref_sig_restrict                funpre
% 2.00/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.00/1.00  --abstr_ref_under                       []
% 2.00/1.00  
% 2.00/1.00  ------ SAT Options
% 2.00/1.00  
% 2.00/1.00  --sat_mode                              false
% 2.00/1.00  --sat_fm_restart_options                ""
% 2.00/1.00  --sat_gr_def                            false
% 2.00/1.00  --sat_epr_types                         true
% 2.00/1.00  --sat_non_cyclic_types                  false
% 2.00/1.00  --sat_finite_models                     false
% 2.00/1.00  --sat_fm_lemmas                         false
% 2.00/1.00  --sat_fm_prep                           false
% 2.00/1.00  --sat_fm_uc_incr                        true
% 2.00/1.00  --sat_out_model                         small
% 2.00/1.00  --sat_out_clauses                       false
% 2.00/1.00  
% 2.00/1.00  ------ QBF Options
% 2.00/1.00  
% 2.00/1.00  --qbf_mode                              false
% 2.00/1.00  --qbf_elim_univ                         false
% 2.00/1.00  --qbf_dom_inst                          none
% 2.00/1.00  --qbf_dom_pre_inst                      false
% 2.00/1.00  --qbf_sk_in                             false
% 2.00/1.00  --qbf_pred_elim                         true
% 2.00/1.00  --qbf_split                             512
% 2.00/1.00  
% 2.00/1.00  ------ BMC1 Options
% 2.00/1.00  
% 2.00/1.00  --bmc1_incremental                      false
% 2.00/1.00  --bmc1_axioms                           reachable_all
% 2.00/1.00  --bmc1_min_bound                        0
% 2.00/1.00  --bmc1_max_bound                        -1
% 2.00/1.00  --bmc1_max_bound_default                -1
% 2.00/1.00  --bmc1_symbol_reachability              true
% 2.00/1.00  --bmc1_property_lemmas                  false
% 2.00/1.00  --bmc1_k_induction                      false
% 2.00/1.00  --bmc1_non_equiv_states                 false
% 2.00/1.00  --bmc1_deadlock                         false
% 2.00/1.00  --bmc1_ucm                              false
% 2.00/1.00  --bmc1_add_unsat_core                   none
% 2.00/1.00  --bmc1_unsat_core_children              false
% 2.00/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.00/1.00  --bmc1_out_stat                         full
% 2.00/1.00  --bmc1_ground_init                      false
% 2.00/1.00  --bmc1_pre_inst_next_state              false
% 2.00/1.00  --bmc1_pre_inst_state                   false
% 2.00/1.00  --bmc1_pre_inst_reach_state             false
% 2.00/1.00  --bmc1_out_unsat_core                   false
% 2.00/1.00  --bmc1_aig_witness_out                  false
% 2.00/1.00  --bmc1_verbose                          false
% 2.00/1.00  --bmc1_dump_clauses_tptp                false
% 2.00/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.00/1.00  --bmc1_dump_file                        -
% 2.00/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.00/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.00/1.00  --bmc1_ucm_extend_mode                  1
% 2.00/1.00  --bmc1_ucm_init_mode                    2
% 2.00/1.00  --bmc1_ucm_cone_mode                    none
% 2.00/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.00/1.00  --bmc1_ucm_relax_model                  4
% 2.00/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.00/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.00/1.00  --bmc1_ucm_layered_model                none
% 2.00/1.00  --bmc1_ucm_max_lemma_size               10
% 2.00/1.00  
% 2.00/1.00  ------ AIG Options
% 2.00/1.00  
% 2.00/1.00  --aig_mode                              false
% 2.00/1.00  
% 2.00/1.00  ------ Instantiation Options
% 2.00/1.00  
% 2.00/1.00  --instantiation_flag                    true
% 2.00/1.00  --inst_sos_flag                         false
% 2.00/1.00  --inst_sos_phase                        true
% 2.00/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.00/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.00/1.00  --inst_lit_sel_side                     num_symb
% 2.00/1.00  --inst_solver_per_active                1400
% 2.00/1.00  --inst_solver_calls_frac                1.
% 2.00/1.00  --inst_passive_queue_type               priority_queues
% 2.00/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.00/1.00  --inst_passive_queues_freq              [25;2]
% 2.00/1.00  --inst_dismatching                      true
% 2.00/1.00  --inst_eager_unprocessed_to_passive     true
% 2.00/1.00  --inst_prop_sim_given                   true
% 2.00/1.00  --inst_prop_sim_new                     false
% 2.00/1.00  --inst_subs_new                         false
% 2.00/1.00  --inst_eq_res_simp                      false
% 2.00/1.00  --inst_subs_given                       false
% 2.00/1.00  --inst_orphan_elimination               true
% 2.00/1.00  --inst_learning_loop_flag               true
% 2.00/1.00  --inst_learning_start                   3000
% 2.00/1.00  --inst_learning_factor                  2
% 2.00/1.00  --inst_start_prop_sim_after_learn       3
% 2.00/1.00  --inst_sel_renew                        solver
% 2.00/1.00  --inst_lit_activity_flag                true
% 2.00/1.00  --inst_restr_to_given                   false
% 2.00/1.00  --inst_activity_threshold               500
% 2.00/1.00  --inst_out_proof                        true
% 2.00/1.00  
% 2.00/1.00  ------ Resolution Options
% 2.00/1.00  
% 2.00/1.00  --resolution_flag                       true
% 2.00/1.00  --res_lit_sel                           adaptive
% 2.00/1.00  --res_lit_sel_side                      none
% 2.00/1.00  --res_ordering                          kbo
% 2.00/1.00  --res_to_prop_solver                    active
% 2.00/1.00  --res_prop_simpl_new                    false
% 2.00/1.00  --res_prop_simpl_given                  true
% 2.00/1.00  --res_passive_queue_type                priority_queues
% 2.00/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.00/1.00  --res_passive_queues_freq               [15;5]
% 2.00/1.00  --res_forward_subs                      full
% 2.00/1.00  --res_backward_subs                     full
% 2.00/1.00  --res_forward_subs_resolution           true
% 2.00/1.00  --res_backward_subs_resolution          true
% 2.00/1.00  --res_orphan_elimination                true
% 2.00/1.00  --res_time_limit                        2.
% 2.00/1.00  --res_out_proof                         true
% 2.00/1.00  
% 2.00/1.00  ------ Superposition Options
% 2.00/1.00  
% 2.00/1.00  --superposition_flag                    true
% 2.00/1.00  --sup_passive_queue_type                priority_queues
% 2.00/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.00/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.00/1.00  --demod_completeness_check              fast
% 2.00/1.00  --demod_use_ground                      true
% 2.00/1.00  --sup_to_prop_solver                    passive
% 2.00/1.00  --sup_prop_simpl_new                    true
% 2.00/1.00  --sup_prop_simpl_given                  true
% 2.00/1.00  --sup_fun_splitting                     false
% 2.00/1.00  --sup_smt_interval                      50000
% 2.00/1.00  
% 2.00/1.00  ------ Superposition Simplification Setup
% 2.00/1.00  
% 2.00/1.00  --sup_indices_passive                   []
% 2.00/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.00/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.00  --sup_full_bw                           [BwDemod]
% 2.00/1.00  --sup_immed_triv                        [TrivRules]
% 2.00/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.00/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.00  --sup_immed_bw_main                     []
% 2.00/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.00/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/1.00  
% 2.00/1.00  ------ Combination Options
% 2.00/1.00  
% 2.00/1.00  --comb_res_mult                         3
% 2.00/1.00  --comb_sup_mult                         2
% 2.00/1.00  --comb_inst_mult                        10
% 2.00/1.00  
% 2.00/1.00  ------ Debug Options
% 2.00/1.00  
% 2.00/1.00  --dbg_backtrace                         false
% 2.00/1.00  --dbg_dump_prop_clauses                 false
% 2.00/1.00  --dbg_dump_prop_clauses_file            -
% 2.00/1.00  --dbg_out_stat                          false
% 2.00/1.00  ------ Parsing...
% 2.00/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.00/1.00  
% 2.00/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.00/1.00  
% 2.00/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.00/1.00  
% 2.00/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.00/1.00  ------ Proving...
% 2.00/1.00  ------ Problem Properties 
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  clauses                                 20
% 2.00/1.00  conjectures                             2
% 2.00/1.00  EPR                                     5
% 2.00/1.00  Horn                                    14
% 2.00/1.00  unary                                   9
% 2.00/1.00  binary                                  8
% 2.00/1.00  lits                                    40
% 2.00/1.00  lits eq                                 13
% 2.00/1.00  fd_pure                                 0
% 2.00/1.00  fd_pseudo                               0
% 2.00/1.00  fd_cond                                 2
% 2.00/1.00  fd_pseudo_cond                          0
% 2.00/1.00  AC symbols                              0
% 2.00/1.00  
% 2.00/1.00  ------ Schedule dynamic 5 is on 
% 2.00/1.00  
% 2.00/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  ------ 
% 2.00/1.00  Current options:
% 2.00/1.00  ------ 
% 2.00/1.00  
% 2.00/1.00  ------ Input Options
% 2.00/1.00  
% 2.00/1.00  --out_options                           all
% 2.00/1.00  --tptp_safe_out                         true
% 2.00/1.00  --problem_path                          ""
% 2.00/1.00  --include_path                          ""
% 2.00/1.00  --clausifier                            res/vclausify_rel
% 2.00/1.00  --clausifier_options                    --mode clausify
% 2.00/1.00  --stdin                                 false
% 2.00/1.00  --stats_out                             all
% 2.00/1.00  
% 2.00/1.00  ------ General Options
% 2.00/1.00  
% 2.00/1.00  --fof                                   false
% 2.00/1.00  --time_out_real                         305.
% 2.00/1.00  --time_out_virtual                      -1.
% 2.00/1.00  --symbol_type_check                     false
% 2.00/1.00  --clausify_out                          false
% 2.00/1.00  --sig_cnt_out                           false
% 2.00/1.00  --trig_cnt_out                          false
% 2.00/1.00  --trig_cnt_out_tolerance                1.
% 2.00/1.00  --trig_cnt_out_sk_spl                   false
% 2.00/1.00  --abstr_cl_out                          false
% 2.00/1.00  
% 2.00/1.00  ------ Global Options
% 2.00/1.00  
% 2.00/1.00  --schedule                              default
% 2.00/1.00  --add_important_lit                     false
% 2.00/1.00  --prop_solver_per_cl                    1000
% 2.00/1.00  --min_unsat_core                        false
% 2.00/1.00  --soft_assumptions                      false
% 2.00/1.00  --soft_lemma_size                       3
% 2.00/1.00  --prop_impl_unit_size                   0
% 2.00/1.00  --prop_impl_unit                        []
% 2.00/1.00  --share_sel_clauses                     true
% 2.00/1.00  --reset_solvers                         false
% 2.00/1.00  --bc_imp_inh                            [conj_cone]
% 2.00/1.00  --conj_cone_tolerance                   3.
% 2.00/1.00  --extra_neg_conj                        none
% 2.00/1.00  --large_theory_mode                     true
% 2.00/1.00  --prolific_symb_bound                   200
% 2.00/1.00  --lt_threshold                          2000
% 2.00/1.00  --clause_weak_htbl                      true
% 2.00/1.00  --gc_record_bc_elim                     false
% 2.00/1.00  
% 2.00/1.00  ------ Preprocessing Options
% 2.00/1.00  
% 2.00/1.00  --preprocessing_flag                    true
% 2.00/1.00  --time_out_prep_mult                    0.1
% 2.00/1.00  --splitting_mode                        input
% 2.00/1.00  --splitting_grd                         true
% 2.00/1.00  --splitting_cvd                         false
% 2.00/1.00  --splitting_cvd_svl                     false
% 2.00/1.00  --splitting_nvd                         32
% 2.00/1.00  --sub_typing                            true
% 2.00/1.00  --prep_gs_sim                           true
% 2.00/1.00  --prep_unflatten                        true
% 2.00/1.00  --prep_res_sim                          true
% 2.00/1.00  --prep_upred                            true
% 2.00/1.00  --prep_sem_filter                       exhaustive
% 2.00/1.00  --prep_sem_filter_out                   false
% 2.00/1.00  --pred_elim                             true
% 2.00/1.00  --res_sim_input                         true
% 2.00/1.00  --eq_ax_congr_red                       true
% 2.00/1.00  --pure_diseq_elim                       true
% 2.00/1.00  --brand_transform                       false
% 2.00/1.00  --non_eq_to_eq                          false
% 2.00/1.00  --prep_def_merge                        true
% 2.00/1.00  --prep_def_merge_prop_impl              false
% 2.00/1.00  --prep_def_merge_mbd                    true
% 2.00/1.00  --prep_def_merge_tr_red                 false
% 2.00/1.00  --prep_def_merge_tr_cl                  false
% 2.00/1.00  --smt_preprocessing                     true
% 2.00/1.00  --smt_ac_axioms                         fast
% 2.00/1.00  --preprocessed_out                      false
% 2.00/1.00  --preprocessed_stats                    false
% 2.00/1.00  
% 2.00/1.00  ------ Abstraction refinement Options
% 2.00/1.00  
% 2.00/1.00  --abstr_ref                             []
% 2.00/1.00  --abstr_ref_prep                        false
% 2.00/1.00  --abstr_ref_until_sat                   false
% 2.00/1.00  --abstr_ref_sig_restrict                funpre
% 2.00/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.00/1.00  --abstr_ref_under                       []
% 2.00/1.00  
% 2.00/1.00  ------ SAT Options
% 2.00/1.00  
% 2.00/1.00  --sat_mode                              false
% 2.00/1.00  --sat_fm_restart_options                ""
% 2.00/1.00  --sat_gr_def                            false
% 2.00/1.00  --sat_epr_types                         true
% 2.00/1.00  --sat_non_cyclic_types                  false
% 2.00/1.00  --sat_finite_models                     false
% 2.00/1.00  --sat_fm_lemmas                         false
% 2.00/1.00  --sat_fm_prep                           false
% 2.00/1.00  --sat_fm_uc_incr                        true
% 2.00/1.00  --sat_out_model                         small
% 2.00/1.00  --sat_out_clauses                       false
% 2.00/1.00  
% 2.00/1.00  ------ QBF Options
% 2.00/1.00  
% 2.00/1.00  --qbf_mode                              false
% 2.00/1.00  --qbf_elim_univ                         false
% 2.00/1.00  --qbf_dom_inst                          none
% 2.00/1.00  --qbf_dom_pre_inst                      false
% 2.00/1.00  --qbf_sk_in                             false
% 2.00/1.00  --qbf_pred_elim                         true
% 2.00/1.00  --qbf_split                             512
% 2.00/1.00  
% 2.00/1.00  ------ BMC1 Options
% 2.00/1.00  
% 2.00/1.00  --bmc1_incremental                      false
% 2.00/1.00  --bmc1_axioms                           reachable_all
% 2.00/1.00  --bmc1_min_bound                        0
% 2.00/1.00  --bmc1_max_bound                        -1
% 2.00/1.00  --bmc1_max_bound_default                -1
% 2.00/1.00  --bmc1_symbol_reachability              true
% 2.00/1.00  --bmc1_property_lemmas                  false
% 2.00/1.00  --bmc1_k_induction                      false
% 2.00/1.00  --bmc1_non_equiv_states                 false
% 2.00/1.00  --bmc1_deadlock                         false
% 2.00/1.00  --bmc1_ucm                              false
% 2.00/1.00  --bmc1_add_unsat_core                   none
% 2.00/1.00  --bmc1_unsat_core_children              false
% 2.00/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.00/1.00  --bmc1_out_stat                         full
% 2.00/1.00  --bmc1_ground_init                      false
% 2.00/1.00  --bmc1_pre_inst_next_state              false
% 2.00/1.00  --bmc1_pre_inst_state                   false
% 2.00/1.00  --bmc1_pre_inst_reach_state             false
% 2.00/1.00  --bmc1_out_unsat_core                   false
% 2.00/1.00  --bmc1_aig_witness_out                  false
% 2.00/1.00  --bmc1_verbose                          false
% 2.00/1.00  --bmc1_dump_clauses_tptp                false
% 2.00/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.00/1.00  --bmc1_dump_file                        -
% 2.00/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.00/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.00/1.00  --bmc1_ucm_extend_mode                  1
% 2.00/1.00  --bmc1_ucm_init_mode                    2
% 2.00/1.00  --bmc1_ucm_cone_mode                    none
% 2.00/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.00/1.00  --bmc1_ucm_relax_model                  4
% 2.00/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.00/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.00/1.00  --bmc1_ucm_layered_model                none
% 2.00/1.00  --bmc1_ucm_max_lemma_size               10
% 2.00/1.00  
% 2.00/1.00  ------ AIG Options
% 2.00/1.00  
% 2.00/1.00  --aig_mode                              false
% 2.00/1.00  
% 2.00/1.00  ------ Instantiation Options
% 2.00/1.00  
% 2.00/1.00  --instantiation_flag                    true
% 2.00/1.00  --inst_sos_flag                         false
% 2.00/1.00  --inst_sos_phase                        true
% 2.00/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.00/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.00/1.00  --inst_lit_sel_side                     none
% 2.00/1.00  --inst_solver_per_active                1400
% 2.00/1.00  --inst_solver_calls_frac                1.
% 2.00/1.00  --inst_passive_queue_type               priority_queues
% 2.00/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.00/1.00  --inst_passive_queues_freq              [25;2]
% 2.00/1.00  --inst_dismatching                      true
% 2.00/1.00  --inst_eager_unprocessed_to_passive     true
% 2.00/1.00  --inst_prop_sim_given                   true
% 2.00/1.00  --inst_prop_sim_new                     false
% 2.00/1.00  --inst_subs_new                         false
% 2.00/1.00  --inst_eq_res_simp                      false
% 2.00/1.00  --inst_subs_given                       false
% 2.00/1.00  --inst_orphan_elimination               true
% 2.00/1.00  --inst_learning_loop_flag               true
% 2.00/1.00  --inst_learning_start                   3000
% 2.00/1.00  --inst_learning_factor                  2
% 2.00/1.00  --inst_start_prop_sim_after_learn       3
% 2.00/1.00  --inst_sel_renew                        solver
% 2.00/1.00  --inst_lit_activity_flag                true
% 2.00/1.00  --inst_restr_to_given                   false
% 2.00/1.00  --inst_activity_threshold               500
% 2.00/1.00  --inst_out_proof                        true
% 2.00/1.00  
% 2.00/1.00  ------ Resolution Options
% 2.00/1.00  
% 2.00/1.00  --resolution_flag                       false
% 2.00/1.00  --res_lit_sel                           adaptive
% 2.00/1.00  --res_lit_sel_side                      none
% 2.00/1.00  --res_ordering                          kbo
% 2.00/1.00  --res_to_prop_solver                    active
% 2.00/1.00  --res_prop_simpl_new                    false
% 2.00/1.00  --res_prop_simpl_given                  true
% 2.00/1.00  --res_passive_queue_type                priority_queues
% 2.00/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.00/1.00  --res_passive_queues_freq               [15;5]
% 2.00/1.00  --res_forward_subs                      full
% 2.00/1.00  --res_backward_subs                     full
% 2.00/1.00  --res_forward_subs_resolution           true
% 2.00/1.00  --res_backward_subs_resolution          true
% 2.00/1.00  --res_orphan_elimination                true
% 2.00/1.00  --res_time_limit                        2.
% 2.00/1.00  --res_out_proof                         true
% 2.00/1.00  
% 2.00/1.00  ------ Superposition Options
% 2.00/1.00  
% 2.00/1.00  --superposition_flag                    true
% 2.00/1.00  --sup_passive_queue_type                priority_queues
% 2.00/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.00/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.00/1.00  --demod_completeness_check              fast
% 2.00/1.00  --demod_use_ground                      true
% 2.00/1.00  --sup_to_prop_solver                    passive
% 2.00/1.00  --sup_prop_simpl_new                    true
% 2.00/1.00  --sup_prop_simpl_given                  true
% 2.00/1.00  --sup_fun_splitting                     false
% 2.00/1.00  --sup_smt_interval                      50000
% 2.00/1.00  
% 2.00/1.00  ------ Superposition Simplification Setup
% 2.00/1.00  
% 2.00/1.00  --sup_indices_passive                   []
% 2.00/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.00/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.00/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.00  --sup_full_bw                           [BwDemod]
% 2.00/1.00  --sup_immed_triv                        [TrivRules]
% 2.00/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.00/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.00  --sup_immed_bw_main                     []
% 2.00/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.00/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.00/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.00/1.00  
% 2.00/1.00  ------ Combination Options
% 2.00/1.00  
% 2.00/1.00  --comb_res_mult                         3
% 2.00/1.00  --comb_sup_mult                         2
% 2.00/1.00  --comb_inst_mult                        10
% 2.00/1.00  
% 2.00/1.00  ------ Debug Options
% 2.00/1.00  
% 2.00/1.00  --dbg_backtrace                         false
% 2.00/1.00  --dbg_dump_prop_clauses                 false
% 2.00/1.00  --dbg_dump_prop_clauses_file            -
% 2.00/1.00  --dbg_out_stat                          false
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  ------ Proving...
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  % SZS status Theorem for theBenchmark.p
% 2.00/1.00  
% 2.00/1.00   Resolution empty clause
% 2.00/1.00  
% 2.00/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.00/1.00  
% 2.00/1.00  fof(f3,axiom,(
% 2.00/1.00    v1_xboole_0(k1_xboole_0)),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f48,plain,(
% 2.00/1.00    v1_xboole_0(k1_xboole_0)),
% 2.00/1.00    inference(cnf_transformation,[],[f3])).
% 2.00/1.00  
% 2.00/1.00  fof(f9,axiom,(
% 2.00/1.00    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f21,plain,(
% 2.00/1.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.00/1.00    inference(ennf_transformation,[],[f9])).
% 2.00/1.00  
% 2.00/1.00  fof(f55,plain,(
% 2.00/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f21])).
% 2.00/1.00  
% 2.00/1.00  fof(f11,axiom,(
% 2.00/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f23,plain,(
% 2.00/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.00/1.00    inference(ennf_transformation,[],[f11])).
% 2.00/1.00  
% 2.00/1.00  fof(f24,plain,(
% 2.00/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.00/1.00    inference(flattening,[],[f23])).
% 2.00/1.00  
% 2.00/1.00  fof(f40,plain,(
% 2.00/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) => (! [X6,X5,X4,X3,X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK2(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK2(X0),X0)))),
% 2.00/1.00    introduced(choice_axiom,[])).
% 2.00/1.00  
% 2.00/1.00  fof(f41,plain,(
% 2.00/1.00    ! [X0] : ((! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK2(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 2.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f40])).
% 2.00/1.00  
% 2.00/1.00  fof(f57,plain,(
% 2.00/1.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.00/1.00    inference(cnf_transformation,[],[f41])).
% 2.00/1.00  
% 2.00/1.00  fof(f1,axiom,(
% 2.00/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f45,plain,(
% 2.00/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f1])).
% 2.00/1.00  
% 2.00/1.00  fof(f4,axiom,(
% 2.00/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f19,plain,(
% 2.00/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.00/1.00    inference(rectify,[],[f4])).
% 2.00/1.00  
% 2.00/1.00  fof(f20,plain,(
% 2.00/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.00/1.00    inference(ennf_transformation,[],[f19])).
% 2.00/1.00  
% 2.00/1.00  fof(f38,plain,(
% 2.00/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 2.00/1.00    introduced(choice_axiom,[])).
% 2.00/1.00  
% 2.00/1.00  fof(f39,plain,(
% 2.00/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f38])).
% 2.00/1.00  
% 2.00/1.00  fof(f50,plain,(
% 2.00/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.00/1.00    inference(cnf_transformation,[],[f39])).
% 2.00/1.00  
% 2.00/1.00  fof(f17,conjecture,(
% 2.00/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f18,negated_conjecture,(
% 2.00/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.00/1.00    inference(negated_conjecture,[],[f17])).
% 2.00/1.00  
% 2.00/1.00  fof(f32,plain,(
% 2.00/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 2.00/1.00    inference(ennf_transformation,[],[f18])).
% 2.00/1.00  
% 2.00/1.00  fof(f33,plain,(
% 2.00/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 2.00/1.00    inference(flattening,[],[f32])).
% 2.00/1.00  
% 2.00/1.00  fof(f43,plain,(
% 2.00/1.00    ( ! [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK4))) )),
% 2.00/1.00    introduced(choice_axiom,[])).
% 2.00/1.00  
% 2.00/1.00  fof(f42,plain,(
% 2.00/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 2.00/1.00    introduced(choice_axiom,[])).
% 2.00/1.00  
% 2.00/1.00  fof(f44,plain,(
% 2.00/1.00    (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 2.00/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f43,f42])).
% 2.00/1.00  
% 2.00/1.00  fof(f70,plain,(
% 2.00/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))),
% 2.00/1.00    inference(cnf_transformation,[],[f44])).
% 2.00/1.00  
% 2.00/1.00  fof(f14,axiom,(
% 2.00/1.00    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f61,plain,(
% 2.00/1.00    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.00/1.00    inference(cnf_transformation,[],[f14])).
% 2.00/1.00  
% 2.00/1.00  fof(f78,plain,(
% 2.00/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))),
% 2.00/1.00    inference(definition_unfolding,[],[f70,f61])).
% 2.00/1.00  
% 2.00/1.00  fof(f68,plain,(
% 2.00/1.00    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 2.00/1.00    inference(cnf_transformation,[],[f44])).
% 2.00/1.00  
% 2.00/1.00  fof(f80,plain,(
% 2.00/1.00    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 2.00/1.00    inference(definition_unfolding,[],[f68,f61])).
% 2.00/1.00  
% 2.00/1.00  fof(f69,plain,(
% 2.00/1.00    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 2.00/1.00    inference(cnf_transformation,[],[f44])).
% 2.00/1.00  
% 2.00/1.00  fof(f79,plain,(
% 2.00/1.00    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 2.00/1.00    inference(definition_unfolding,[],[f69,f61])).
% 2.00/1.00  
% 2.00/1.00  fof(f16,axiom,(
% 2.00/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f30,plain,(
% 2.00/1.00    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.00/1.00    inference(ennf_transformation,[],[f16])).
% 2.00/1.00  
% 2.00/1.00  fof(f31,plain,(
% 2.00/1.00    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.00/1.00    inference(flattening,[],[f30])).
% 2.00/1.00  
% 2.00/1.00  fof(f63,plain,(
% 2.00/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f31])).
% 2.00/1.00  
% 2.00/1.00  fof(f77,plain,(
% 2.00/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.00/1.00    inference(definition_unfolding,[],[f63,f61,f61,f61,f61])).
% 2.00/1.00  
% 2.00/1.00  fof(f67,plain,(
% 2.00/1.00    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))),
% 2.00/1.00    inference(cnf_transformation,[],[f44])).
% 2.00/1.00  
% 2.00/1.00  fof(f81,plain,(
% 2.00/1.00    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))),
% 2.00/1.00    inference(definition_unfolding,[],[f67,f61])).
% 2.00/1.00  
% 2.00/1.00  fof(f66,plain,(
% 2.00/1.00    ~v1_xboole_0(sK4)),
% 2.00/1.00    inference(cnf_transformation,[],[f44])).
% 2.00/1.00  
% 2.00/1.00  fof(f13,axiom,(
% 2.00/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f26,plain,(
% 2.00/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.00/1.00    inference(ennf_transformation,[],[f13])).
% 2.00/1.00  
% 2.00/1.00  fof(f27,plain,(
% 2.00/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.00/1.00    inference(flattening,[],[f26])).
% 2.00/1.00  
% 2.00/1.00  fof(f60,plain,(
% 2.00/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f27])).
% 2.00/1.00  
% 2.00/1.00  fof(f64,plain,(
% 2.00/1.00    ~v2_struct_0(sK3)),
% 2.00/1.00    inference(cnf_transformation,[],[f44])).
% 2.00/1.00  
% 2.00/1.00  fof(f65,plain,(
% 2.00/1.00    l1_struct_0(sK3)),
% 2.00/1.00    inference(cnf_transformation,[],[f44])).
% 2.00/1.00  
% 2.00/1.00  fof(f12,axiom,(
% 2.00/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f25,plain,(
% 2.00/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.00/1.00    inference(ennf_transformation,[],[f12])).
% 2.00/1.00  
% 2.00/1.00  fof(f59,plain,(
% 2.00/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f25])).
% 2.00/1.00  
% 2.00/1.00  fof(f10,axiom,(
% 2.00/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f22,plain,(
% 2.00/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.00/1.00    inference(ennf_transformation,[],[f10])).
% 2.00/1.00  
% 2.00/1.00  fof(f56,plain,(
% 2.00/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.00/1.00    inference(cnf_transformation,[],[f22])).
% 2.00/1.00  
% 2.00/1.00  fof(f5,axiom,(
% 2.00/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f51,plain,(
% 2.00/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.00/1.00    inference(cnf_transformation,[],[f5])).
% 2.00/1.00  
% 2.00/1.00  fof(f75,plain,(
% 2.00/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.00/1.00    inference(definition_unfolding,[],[f56,f51])).
% 2.00/1.00  
% 2.00/1.00  fof(f15,axiom,(
% 2.00/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f28,plain,(
% 2.00/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.00/1.00    inference(ennf_transformation,[],[f15])).
% 2.00/1.00  
% 2.00/1.00  fof(f29,plain,(
% 2.00/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.00/1.00    inference(flattening,[],[f28])).
% 2.00/1.00  
% 2.00/1.00  fof(f62,plain,(
% 2.00/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f29])).
% 2.00/1.00  
% 2.00/1.00  fof(f76,plain,(
% 2.00/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.00/1.00    inference(definition_unfolding,[],[f62,f61,f61,f61,f61])).
% 2.00/1.00  
% 2.00/1.00  fof(f71,plain,(
% 2.00/1.00    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4),
% 2.00/1.00    inference(cnf_transformation,[],[f44])).
% 2.00/1.00  
% 2.00/1.00  fof(f6,axiom,(
% 2.00/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f52,plain,(
% 2.00/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.00/1.00    inference(cnf_transformation,[],[f6])).
% 2.00/1.00  
% 2.00/1.00  fof(f8,axiom,(
% 2.00/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f54,plain,(
% 2.00/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f8])).
% 2.00/1.00  
% 2.00/1.00  fof(f72,plain,(
% 2.00/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.00/1.00    inference(definition_unfolding,[],[f54,f51])).
% 2.00/1.00  
% 2.00/1.00  fof(f73,plain,(
% 2.00/1.00    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 2.00/1.00    inference(definition_unfolding,[],[f52,f72])).
% 2.00/1.00  
% 2.00/1.00  fof(f7,axiom,(
% 2.00/1.00    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.00/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.00/1.00  
% 2.00/1.00  fof(f53,plain,(
% 2.00/1.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.00/1.00    inference(cnf_transformation,[],[f7])).
% 2.00/1.00  
% 2.00/1.00  fof(f74,plain,(
% 2.00/1.00    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 2.00/1.00    inference(definition_unfolding,[],[f53,f51])).
% 2.00/1.00  
% 2.00/1.00  cnf(c_3,plain,
% 2.00/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_929,plain,
% 2.00/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_8,plain,
% 2.00/1.00      ( r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 2.00/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_926,plain,
% 2.00/1.00      ( r1_xboole_0(k1_tarski(X0),X1) = iProver_top
% 2.00/1.00      | r2_hidden(X0,X1) = iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_11,plain,
% 2.00/1.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.00/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_924,plain,
% 2.00/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_0,plain,
% 2.00/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_4,plain,
% 2.00/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 2.00/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_928,plain,
% 2.00/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 2.00/1.00      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1500,plain,
% 2.00/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 2.00/1.00      | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
% 2.00/1.00      inference(superposition,[status(thm)],[c_0,c_928]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1675,plain,
% 2.00/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X1,X0) != iProver_top ),
% 2.00/1.00      inference(superposition,[status(thm)],[c_924,c_1500]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_2006,plain,
% 2.00/1.00      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0
% 2.00/1.00      | r2_hidden(X1,X0) = iProver_top ),
% 2.00/1.00      inference(superposition,[status(thm)],[c_926,c_1675]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_17,negated_conjecture,
% 2.00/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
% 2.00/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_19,negated_conjecture,
% 2.00/1.00      ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.00/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_18,negated_conjecture,
% 2.00/1.00      ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.00/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_15,plain,
% 2.00/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.00/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.00/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.00/1.00      | ~ r2_hidden(X2,X0)
% 2.00/1.00      | ~ v1_xboole_0(X2)
% 2.00/1.00      | v1_xboole_0(X1)
% 2.00/1.00      | v1_xboole_0(X0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_20,negated_conjecture,
% 2.00/1.00      ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
% 2.00/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_238,plain,
% 2.00/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.00/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.00/1.00      | ~ r2_hidden(X2,X0)
% 2.00/1.00      | ~ v1_xboole_0(X2)
% 2.00/1.00      | v1_xboole_0(X0)
% 2.00/1.00      | v1_xboole_0(X1)
% 2.00/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.00/1.00      | sK4 != X0 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_239,plain,
% 2.00/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.00/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.00/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.00/1.00      | ~ r2_hidden(X1,sK4)
% 2.00/1.00      | ~ v1_xboole_0(X1)
% 2.00/1.00      | v1_xboole_0(X0)
% 2.00/1.00      | v1_xboole_0(sK4)
% 2.00/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_238]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_21,negated_conjecture,
% 2.00/1.00      ( ~ v1_xboole_0(sK4) ),
% 2.00/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_241,plain,
% 2.00/1.00      ( v1_xboole_0(X0)
% 2.00/1.00      | ~ v1_xboole_0(X1)
% 2.00/1.00      | ~ r2_hidden(X1,sK4)
% 2.00/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.00/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.00/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.00/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.00/1.00      inference(global_propositional_subsumption,[status(thm)],[c_239,c_21]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_242,plain,
% 2.00/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.00/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.00/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.00/1.00      | ~ r2_hidden(X1,sK4)
% 2.00/1.00      | ~ v1_xboole_0(X1)
% 2.00/1.00      | v1_xboole_0(X0)
% 2.00/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.00/1.00      inference(renaming,[status(thm)],[c_241]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_323,plain,
% 2.00/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.00/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.00/1.00      | ~ r2_hidden(X1,sK4)
% 2.00/1.00      | ~ v1_xboole_0(X1)
% 2.00/1.00      | v1_xboole_0(X0)
% 2.00/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.00/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.00/1.00      | sK4 != sK4 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_242]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_368,plain,
% 2.00/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.00/1.00      | ~ r2_hidden(X1,sK4)
% 2.00/1.00      | ~ v1_xboole_0(X1)
% 2.00/1.00      | v1_xboole_0(X0)
% 2.00/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.00/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.00/1.00      | sK4 != sK4 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_323]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_409,plain,
% 2.00/1.00      ( ~ r2_hidden(X0,sK4)
% 2.00/1.00      | ~ v1_xboole_0(X0)
% 2.00/1.00      | v1_xboole_0(X1)
% 2.00/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.00/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.00/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.00/1.00      | sK4 != sK4 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_368]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_514,plain,
% 2.00/1.00      ( ~ r2_hidden(X0,sK4)
% 2.00/1.00      | ~ v1_xboole_0(X0)
% 2.00/1.00      | v1_xboole_0(X1)
% 2.00/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.00/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.00/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
% 2.00/1.00      inference(equality_resolution_simp,[status(thm)],[c_409]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_648,plain,
% 2.00/1.00      ( ~ r2_hidden(X0,sK4) | ~ v1_xboole_0(X0) | ~ sP1_iProver_split ),
% 2.00/1.00      inference(splitting,
% 2.00/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.00/1.00                [c_514]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_920,plain,
% 2.00/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 2.00/1.00      | v1_xboole_0(X0) != iProver_top
% 2.00/1.00      | sP1_iProver_split != iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_2570,plain,
% 2.00/1.00      ( k3_xboole_0(sK4,k1_tarski(X0)) = k1_xboole_0
% 2.00/1.00      | v1_xboole_0(X0) != iProver_top
% 2.00/1.00      | sP1_iProver_split != iProver_top ),
% 2.00/1.00      inference(superposition,[status(thm)],[c_2006,c_920]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_649,plain,
% 2.00/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 2.00/1.00      inference(splitting,
% 2.00/1.00                [splitting(split),new_symbols(definition,[])],
% 2.00/1.00                [c_514]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_682,plain,
% 2.00/1.00      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_13,plain,
% 2.00/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.00/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_23,negated_conjecture,
% 2.00/1.00      ( ~ v2_struct_0(sK3) ),
% 2.00/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_275,plain,
% 2.00/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_276,plain,
% 2.00/1.00      ( ~ l1_struct_0(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_275]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_22,negated_conjecture,
% 2.00/1.00      ( l1_struct_0(sK3) ),
% 2.00/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_278,plain,
% 2.00/1.00      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.00/1.00      inference(global_propositional_subsumption,[status(thm)],[c_276,c_22]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_922,plain,
% 2.00/1.00      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_12,plain,
% 2.00/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.00/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_317,plain,
% 2.00/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_318,plain,
% 2.00/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_317]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_938,plain,
% 2.00/1.00      ( v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 2.00/1.00      inference(light_normalisation,[status(thm)],[c_922,c_318]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_647,plain,
% 2.00/1.00      ( v1_xboole_0(X0)
% 2.00/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.00/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.00/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 2.00/1.00      | ~ sP0_iProver_split ),
% 2.00/1.00      inference(splitting,
% 2.00/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.00/1.00                [c_514]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_921,plain,
% 2.00/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.00/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.00/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 2.00/1.00      | v1_xboole_0(X0) = iProver_top
% 2.00/1.00      | sP0_iProver_split != iProver_top ),
% 2.00/1.00      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1398,plain,
% 2.00/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 2.00/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.00/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 2.00/1.00      | sP0_iProver_split != iProver_top ),
% 2.00/1.00      inference(equality_resolution,[status(thm)],[c_921]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1450,plain,
% 2.00/1.00      ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 2.00/1.00      | sP0_iProver_split != iProver_top ),
% 2.00/1.00      inference(equality_resolution_simp,[status(thm)],[c_1398]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_2688,plain,
% 2.00/1.00      ( v1_xboole_0(X0) != iProver_top
% 2.00/1.00      | k3_xboole_0(sK4,k1_tarski(X0)) = k1_xboole_0 ),
% 2.00/1.00      inference(global_propositional_subsumption,
% 2.00/1.00                [status(thm)],
% 2.00/1.00                [c_2570,c_682,c_938,c_1450]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_2689,plain,
% 2.00/1.00      ( k3_xboole_0(sK4,k1_tarski(X0)) = k1_xboole_0
% 2.00/1.00      | v1_xboole_0(X0) != iProver_top ),
% 2.00/1.00      inference(renaming,[status(thm)],[c_2688]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_2696,plain,
% 2.00/1.00      ( k3_xboole_0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
% 2.00/1.00      inference(superposition,[status(thm)],[c_929,c_2689]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_9,plain,
% 2.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.00/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 2.00/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_400,plain,
% 2.00/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 2.00/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X2)
% 2.00/1.00      | sK4 != X0 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_401,plain,
% 2.00/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) = k7_subset_1(X1,sK4,X0)
% 2.00/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X1) ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_400]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1076,plain,
% 2.00/1.00      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
% 2.00/1.00      inference(equality_resolution,[status(thm)],[c_401]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_14,plain,
% 2.00/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.00/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.00/1.00      | v2_struct_0(X1)
% 2.00/1.00      | ~ l1_struct_0(X1)
% 2.00/1.00      | v1_xboole_0(X0)
% 2.00/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
% 2.00/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_286,plain,
% 2.00/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.00/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.00/1.00      | ~ l1_struct_0(X1)
% 2.00/1.00      | v1_xboole_0(X0)
% 2.00/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
% 2.00/1.00      | sK3 != X1 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_287,plain,
% 2.00/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.00/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.00/1.00      | ~ l1_struct_0(sK3)
% 2.00/1.00      | v1_xboole_0(X0)
% 2.00/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_286]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_289,plain,
% 2.00/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.00/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.00/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.00/1.00      | v1_xboole_0(X0)
% 2.00/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 2.00/1.00      inference(global_propositional_subsumption,[status(thm)],[c_287,c_22]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_290,plain,
% 2.00/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.00/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.00/1.00      | v1_xboole_0(X0)
% 2.00/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 2.00/1.00      inference(renaming,[status(thm)],[c_289]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_350,plain,
% 2.00/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.00/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.00/1.00      | v1_xboole_0(X0)
% 2.00/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
% 2.00/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 2.00/1.00      | sK4 != X0 ),
% 2.00/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_290]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_351,plain,
% 2.00/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.00/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.00/1.00      | v1_xboole_0(sK4)
% 2.00/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.00/1.00      inference(unflattening,[status(thm)],[c_350]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_353,plain,
% 2.00/1.00      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.00/1.00      inference(global_propositional_subsumption,
% 2.00/1.00                [status(thm)],
% 2.00/1.00                [c_351,c_21,c_19,c_17]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1094,plain,
% 2.00/1.00      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) ),
% 2.00/1.00      inference(demodulation,[status(thm)],[c_1076,c_353]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_16,negated_conjecture,
% 2.00/1.00      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
% 2.00/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_1096,plain,
% 2.00/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) != sK4 ),
% 2.00/1.00      inference(demodulation,[status(thm)],[c_1094,c_16]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_2810,plain,
% 2.00/1.00      ( k5_xboole_0(sK4,k1_xboole_0) != sK4 ),
% 2.00/1.00      inference(demodulation,[status(thm)],[c_2696,c_1096]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_6,plain,
% 2.00/1.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 2.00/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_7,plain,
% 2.00/1.00      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 2.00/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_949,plain,
% 2.00/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.00/1.00      inference(light_normalisation,[status(thm)],[c_6,c_7]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_2816,plain,
% 2.00/1.00      ( sK4 != sK4 ),
% 2.00/1.00      inference(demodulation,[status(thm)],[c_2810,c_949]) ).
% 2.00/1.00  
% 2.00/1.00  cnf(c_2817,plain,
% 2.00/1.00      ( $false ),
% 2.00/1.00      inference(equality_resolution_simp,[status(thm)],[c_2816]) ).
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.00/1.00  
% 2.00/1.00  ------                               Statistics
% 2.00/1.00  
% 2.00/1.00  ------ General
% 2.00/1.00  
% 2.00/1.00  abstr_ref_over_cycles:                  0
% 2.00/1.00  abstr_ref_under_cycles:                 0
% 2.00/1.00  gc_basic_clause_elim:                   0
% 2.00/1.00  forced_gc_time:                         0
% 2.00/1.00  parsing_time:                           0.011
% 2.00/1.00  unif_index_cands_time:                  0.
% 2.00/1.00  unif_index_add_time:                    0.
% 2.00/1.00  orderings_time:                         0.
% 2.00/1.00  out_proof_time:                         0.01
% 2.00/1.00  total_time:                             0.143
% 2.00/1.00  num_of_symbols:                         59
% 2.00/1.00  num_of_terms:                           2215
% 2.00/1.00  
% 2.00/1.00  ------ Preprocessing
% 2.00/1.00  
% 2.00/1.00  num_of_splits:                          2
% 2.00/1.00  num_of_split_atoms:                     2
% 2.00/1.00  num_of_reused_defs:                     0
% 2.00/1.00  num_eq_ax_congr_red:                    19
% 2.00/1.00  num_of_sem_filtered_clauses:            1
% 2.00/1.00  num_of_subtypes:                        0
% 2.00/1.00  monotx_restored_types:                  0
% 2.00/1.00  sat_num_of_epr_types:                   0
% 2.00/1.00  sat_num_of_non_cyclic_types:            0
% 2.00/1.00  sat_guarded_non_collapsed_types:        0
% 2.00/1.00  num_pure_diseq_elim:                    0
% 2.00/1.00  simp_replaced_by:                       0
% 2.00/1.00  res_preprocessed:                       115
% 2.00/1.00  prep_upred:                             0
% 2.00/1.00  prep_unflattend:                        10
% 2.00/1.00  smt_new_axioms:                         0
% 2.00/1.00  pred_elim_cands:                        3
% 2.00/1.00  pred_elim:                              6
% 2.00/1.00  pred_elim_cl:                           6
% 2.00/1.00  pred_elim_cycles:                       8
% 2.00/1.00  merged_defs:                            0
% 2.00/1.00  merged_defs_ncl:                        0
% 2.00/1.00  bin_hyper_res:                          0
% 2.00/1.00  prep_cycles:                            4
% 2.00/1.00  pred_elim_time:                         0.007
% 2.00/1.00  splitting_time:                         0.
% 2.00/1.00  sem_filter_time:                        0.
% 2.00/1.00  monotx_time:                            0.001
% 2.00/1.00  subtype_inf_time:                       0.
% 2.00/1.00  
% 2.00/1.00  ------ Problem properties
% 2.00/1.00  
% 2.00/1.00  clauses:                                20
% 2.00/1.00  conjectures:                            2
% 2.00/1.00  epr:                                    5
% 2.00/1.00  horn:                                   14
% 2.00/1.00  ground:                                 7
% 2.00/1.00  unary:                                  9
% 2.00/1.00  binary:                                 8
% 2.00/1.00  lits:                                   40
% 2.00/1.00  lits_eq:                                13
% 2.00/1.00  fd_pure:                                0
% 2.00/1.00  fd_pseudo:                              0
% 2.00/1.00  fd_cond:                                2
% 2.00/1.00  fd_pseudo_cond:                         0
% 2.00/1.00  ac_symbols:                             0
% 2.00/1.00  
% 2.00/1.00  ------ Propositional Solver
% 2.00/1.00  
% 2.00/1.00  prop_solver_calls:                      27
% 2.00/1.00  prop_fast_solver_calls:                 678
% 2.00/1.00  smt_solver_calls:                       0
% 2.00/1.00  smt_fast_solver_calls:                  0
% 2.00/1.00  prop_num_of_clauses:                    868
% 2.00/1.00  prop_preprocess_simplified:             3759
% 2.00/1.00  prop_fo_subsumed:                       13
% 2.00/1.00  prop_solver_time:                       0.
% 2.00/1.00  smt_solver_time:                        0.
% 2.00/1.00  smt_fast_solver_time:                   0.
% 2.00/1.00  prop_fast_solver_time:                  0.
% 2.00/1.00  prop_unsat_core_time:                   0.
% 2.00/1.00  
% 2.00/1.00  ------ QBF
% 2.00/1.00  
% 2.00/1.00  qbf_q_res:                              0
% 2.00/1.00  qbf_num_tautologies:                    0
% 2.00/1.00  qbf_prep_cycles:                        0
% 2.00/1.00  
% 2.00/1.00  ------ BMC1
% 2.00/1.00  
% 2.00/1.00  bmc1_current_bound:                     -1
% 2.00/1.00  bmc1_last_solved_bound:                 -1
% 2.00/1.00  bmc1_unsat_core_size:                   -1
% 2.00/1.00  bmc1_unsat_core_parents_size:           -1
% 2.00/1.00  bmc1_merge_next_fun:                    0
% 2.00/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.00/1.00  
% 2.00/1.00  ------ Instantiation
% 2.00/1.00  
% 2.00/1.00  inst_num_of_clauses:                    340
% 2.00/1.00  inst_num_in_passive:                    142
% 2.00/1.00  inst_num_in_active:                     174
% 2.00/1.00  inst_num_in_unprocessed:                25
% 2.00/1.00  inst_num_of_loops:                      210
% 2.00/1.00  inst_num_of_learning_restarts:          0
% 2.00/1.00  inst_num_moves_active_passive:          33
% 2.00/1.00  inst_lit_activity:                      0
% 2.00/1.00  inst_lit_activity_moves:                0
% 2.00/1.00  inst_num_tautologies:                   0
% 2.00/1.00  inst_num_prop_implied:                  0
% 2.00/1.00  inst_num_existing_simplified:           0
% 2.00/1.00  inst_num_eq_res_simplified:             0
% 2.00/1.00  inst_num_child_elim:                    0
% 2.00/1.00  inst_num_of_dismatching_blockings:      26
% 2.00/1.00  inst_num_of_non_proper_insts:           228
% 2.00/1.00  inst_num_of_duplicates:                 0
% 2.00/1.00  inst_inst_num_from_inst_to_res:         0
% 2.00/1.00  inst_dismatching_checking_time:         0.
% 2.00/1.00  
% 2.00/1.00  ------ Resolution
% 2.00/1.00  
% 2.00/1.00  res_num_of_clauses:                     0
% 2.00/1.00  res_num_in_passive:                     0
% 2.00/1.00  res_num_in_active:                      0
% 2.00/1.00  res_num_of_loops:                       119
% 2.00/1.00  res_forward_subset_subsumed:            59
% 2.00/1.00  res_backward_subset_subsumed:           4
% 2.00/1.00  res_forward_subsumed:                   0
% 2.00/1.00  res_backward_subsumed:                  0
% 2.00/1.00  res_forward_subsumption_resolution:     0
% 2.00/1.00  res_backward_subsumption_resolution:    0
% 2.00/1.00  res_clause_to_clause_subsumption:       190
% 2.00/1.00  res_orphan_elimination:                 0
% 2.00/1.00  res_tautology_del:                      34
% 2.00/1.00  res_num_eq_res_simplified:              1
% 2.00/1.00  res_num_sel_changes:                    0
% 2.00/1.00  res_moves_from_active_to_pass:          0
% 2.00/1.00  
% 2.00/1.00  ------ Superposition
% 2.00/1.00  
% 2.00/1.00  sup_time_total:                         0.
% 2.00/1.00  sup_time_generating:                    0.
% 2.00/1.00  sup_time_sim_full:                      0.
% 2.00/1.00  sup_time_sim_immed:                     0.
% 2.00/1.00  
% 2.00/1.00  sup_num_of_clauses:                     59
% 2.00/1.00  sup_num_in_active:                      37
% 2.00/1.00  sup_num_in_passive:                     22
% 2.00/1.00  sup_num_of_loops:                       41
% 2.00/1.00  sup_fw_superposition:                   30
% 2.00/1.00  sup_bw_superposition:                   37
% 2.00/1.00  sup_immediate_simplified:               2
% 2.00/1.00  sup_given_eliminated:                   0
% 2.00/1.00  comparisons_done:                       0
% 2.00/1.00  comparisons_avoided:                    0
% 2.00/1.00  
% 2.00/1.00  ------ Simplifications
% 2.00/1.00  
% 2.00/1.00  
% 2.00/1.00  sim_fw_subset_subsumed:                 2
% 2.00/1.00  sim_bw_subset_subsumed:                 0
% 2.00/1.00  sim_fw_subsumed:                        0
% 2.00/1.00  sim_bw_subsumed:                        0
% 2.00/1.00  sim_fw_subsumption_res:                 0
% 2.00/1.00  sim_bw_subsumption_res:                 0
% 2.00/1.00  sim_tautology_del:                      3
% 2.00/1.00  sim_eq_tautology_del:                   1
% 2.00/1.00  sim_eq_res_simp:                        1
% 2.00/1.00  sim_fw_demodulated:                     2
% 2.00/1.00  sim_bw_demodulated:                     4
% 2.00/1.00  sim_light_normalised:                   2
% 2.00/1.00  sim_joinable_taut:                      0
% 2.00/1.00  sim_joinable_simp:                      0
% 2.00/1.00  sim_ac_normalised:                      0
% 2.00/1.00  sim_smt_subsumption:                    0
% 2.00/1.00  
%------------------------------------------------------------------------------
