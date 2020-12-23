%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:04 EST 2020

% Result     : Theorem 31.51s
% Output     : CNFRefutation 31.51s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 509 expanded)
%              Number of clauses        :   78 ( 122 expanded)
%              Number of leaves         :   21 ( 144 expanded)
%              Depth                    :   25
%              Number of atoms          :  453 (2594 expanded)
%              Number of equality atoms :  141 ( 505 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( r1_xboole_0(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( r1_xboole_0(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f40])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f38])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f57,f52])).

fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

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
    inference(ennf_transformation,[],[f19])).

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

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(definition_unfolding,[],[f71,f62])).

fof(f69,plain,(
    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f69,f62])).

fof(f70,plain,(
    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f70,f62])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f64,plain,(
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

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f62,f62,f62,f62])).

fof(f68,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(definition_unfolding,[],[f68,f62])).

fof(f67,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f63,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f63,f62,f62,f62,f62])).

fof(f72,plain,(
    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_32865,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32862,plain,
    ( r1_xboole_0(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_32860,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,negated_conjecture,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32864,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32940,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_32864,c_11])).

cnf(c_33167,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_32860,c_32940])).

cnf(c_33994,plain,
    ( k1_setfam_1(k2_tarski(k1_tarski(X0),X1)) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_32862,c_33167])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_21,negated_conjecture,
    ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_20,negated_conjecture,
    ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_17,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_287,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_288,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_290,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_23])).

cnf(c_291,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_290])).

cnf(c_376,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_291])).

cnf(c_421,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_376])).

cnf(c_462,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_421])).

cnf(c_732,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
    inference(equality_resolution_simp,[status(thm)],[c_462])).

cnf(c_1054,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_732])).

cnf(c_32853,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1054])).

cnf(c_34361,plain,
    ( k1_setfam_1(k2_tarski(k1_tarski(X0),sK4)) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_33994,c_32853])).

cnf(c_1055,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_732])).

cnf(c_1091,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1055])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_324,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_325,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_24,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_44,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_327,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_25,c_24,c_44])).

cnf(c_32855,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_14,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_370,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_371,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_32878,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_32855,c_371])).

cnf(c_1053,plain,
    ( v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_732])).

cnf(c_32854,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1053])).

cnf(c_33139,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_32854])).

cnf(c_33144,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_33139])).

cnf(c_36083,plain,
    ( v1_xboole_0(X0) != iProver_top
    | k1_setfam_1(k2_tarski(k1_tarski(X0),sK4)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34361,c_1091,c_32878,c_33144])).

cnf(c_36084,plain,
    ( k1_setfam_1(k2_tarski(k1_tarski(X0),sK4)) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_36083])).

cnf(c_36091,plain,
    ( k1_setfam_1(k2_tarski(k1_tarski(k1_xboole_0),sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_32865,c_36084])).

cnf(c_8,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32910,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_11])).

cnf(c_33582,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_32910])).

cnf(c_129024,plain,
    ( k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) = k5_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_36091,c_33582])).

cnf(c_7,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_33098,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_7])).

cnf(c_33225,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_33098])).

cnf(c_33580,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_33225,c_32910])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_33590,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_33580,c_6])).

cnf(c_129075,plain,
    ( k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) = sK4 ),
    inference(demodulation,[status(thm)],[c_129024,c_33590])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_453,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_454,plain,
    ( k7_subset_1(X0,sK4,X1) = k4_xboole_0(sK4,X1)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_33021,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,X0) = k4_xboole_0(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_454])).

cnf(c_16,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_335,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_336,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | ~ l1_struct_0(sK3)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_24])).

cnf(c_341,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_403,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_341])).

cnf(c_404,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(sK4)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_406,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_404,c_23,c_21,c_19])).

cnf(c_33053,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_33021,c_406])).

cnf(c_18,negated_conjecture,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33111,plain,
    ( k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) != sK4 ),
    inference(demodulation,[status(thm)],[c_33053,c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_129075,c_33111])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.51/4.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.51/4.50  
% 31.51/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.51/4.50  
% 31.51/4.50  ------  iProver source info
% 31.51/4.50  
% 31.51/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.51/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.51/4.50  git: non_committed_changes: false
% 31.51/4.50  git: last_make_outside_of_git: false
% 31.51/4.50  
% 31.51/4.50  ------ 
% 31.51/4.50  ------ Parsing...
% 31.51/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  ------ Proving...
% 31.51/4.50  ------ Problem Properties 
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  clauses                                 22
% 31.51/4.50  conjectures                             4
% 31.51/4.50  EPR                                     5
% 31.51/4.50  Horn                                    16
% 31.51/4.50  unary                                   11
% 31.51/4.50  binary                                  9
% 31.51/4.50  lits                                    37
% 31.51/4.50  lits eq                                 15
% 31.51/4.50  fd_pure                                 0
% 31.51/4.50  fd_pseudo                               0
% 31.51/4.50  fd_cond                                 2
% 31.51/4.50  fd_pseudo_cond                          0
% 31.51/4.50  AC symbols                              0
% 31.51/4.50  
% 31.51/4.50  ------ Input Options Time Limit: Unbounded
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing...
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 31.51/4.50  Current options:
% 31.51/4.50  ------ 
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing...
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing...
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing...
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing...
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing...
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.51/4.50  
% 31.51/4.50  ------ Proving...
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  % SZS status Theorem for theBenchmark.p
% 31.51/4.50  
% 31.51/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.51/4.50  
% 31.51/4.50  fof(f2,axiom,(
% 31.51/4.50    v1_xboole_0(k1_xboole_0)),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f47,plain,(
% 31.51/4.50    v1_xboole_0(k1_xboole_0)),
% 31.51/4.50    inference(cnf_transformation,[],[f2])).
% 31.51/4.50  
% 31.51/4.50  fof(f9,axiom,(
% 31.51/4.50    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f22,plain,(
% 31.51/4.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 31.51/4.50    inference(ennf_transformation,[],[f9])).
% 31.51/4.50  
% 31.51/4.50  fof(f55,plain,(
% 31.51/4.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 31.51/4.50    inference(cnf_transformation,[],[f22])).
% 31.51/4.50  
% 31.51/4.50  fof(f12,axiom,(
% 31.51/4.50    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f24,plain,(
% 31.51/4.50    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 31.51/4.50    inference(ennf_transformation,[],[f12])).
% 31.51/4.50  
% 31.51/4.50  fof(f40,plain,(
% 31.51/4.50    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) => (r1_xboole_0(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 31.51/4.50    introduced(choice_axiom,[])).
% 31.51/4.50  
% 31.51/4.50  fof(f41,plain,(
% 31.51/4.50    ! [X0] : ((r1_xboole_0(sK2(X0),X0) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 31.51/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f40])).
% 31.51/4.50  
% 31.51/4.50  fof(f58,plain,(
% 31.51/4.50    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 31.51/4.50    inference(cnf_transformation,[],[f41])).
% 31.51/4.50  
% 31.51/4.50  fof(f3,axiom,(
% 31.51/4.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f20,plain,(
% 31.51/4.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 31.51/4.50    inference(rectify,[],[f3])).
% 31.51/4.50  
% 31.51/4.50  fof(f21,plain,(
% 31.51/4.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 31.51/4.50    inference(ennf_transformation,[],[f20])).
% 31.51/4.50  
% 31.51/4.50  fof(f38,plain,(
% 31.51/4.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 31.51/4.50    introduced(choice_axiom,[])).
% 31.51/4.50  
% 31.51/4.50  fof(f39,plain,(
% 31.51/4.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 31.51/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f38])).
% 31.51/4.50  
% 31.51/4.50  fof(f49,plain,(
% 31.51/4.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 31.51/4.50    inference(cnf_transformation,[],[f39])).
% 31.51/4.50  
% 31.51/4.50  fof(f6,axiom,(
% 31.51/4.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f52,plain,(
% 31.51/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 31.51/4.50    inference(cnf_transformation,[],[f6])).
% 31.51/4.50  
% 31.51/4.50  fof(f74,plain,(
% 31.51/4.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 31.51/4.50    inference(definition_unfolding,[],[f49,f52])).
% 31.51/4.50  
% 31.51/4.50  fof(f11,axiom,(
% 31.51/4.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f57,plain,(
% 31.51/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 31.51/4.50    inference(cnf_transformation,[],[f11])).
% 31.51/4.50  
% 31.51/4.50  fof(f76,plain,(
% 31.51/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 31.51/4.50    inference(definition_unfolding,[],[f57,f52])).
% 31.51/4.50  
% 31.51/4.50  fof(f18,conjecture,(
% 31.51/4.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f19,negated_conjecture,(
% 31.51/4.50    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 31.51/4.50    inference(negated_conjecture,[],[f18])).
% 31.51/4.50  
% 31.51/4.50  fof(f32,plain,(
% 31.51/4.50    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 31.51/4.50    inference(ennf_transformation,[],[f19])).
% 31.51/4.50  
% 31.51/4.50  fof(f33,plain,(
% 31.51/4.50    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 31.51/4.50    inference(flattening,[],[f32])).
% 31.51/4.50  
% 31.51/4.50  fof(f43,plain,(
% 31.51/4.50    ( ! [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK4))) )),
% 31.51/4.50    introduced(choice_axiom,[])).
% 31.51/4.50  
% 31.51/4.50  fof(f42,plain,(
% 31.51/4.50    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 31.51/4.50    introduced(choice_axiom,[])).
% 31.51/4.50  
% 31.51/4.50  fof(f44,plain,(
% 31.51/4.50    (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 31.51/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f43,f42])).
% 31.51/4.50  
% 31.51/4.50  fof(f71,plain,(
% 31.51/4.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))),
% 31.51/4.50    inference(cnf_transformation,[],[f44])).
% 31.51/4.50  
% 31.51/4.50  fof(f15,axiom,(
% 31.51/4.50    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f62,plain,(
% 31.51/4.50    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 31.51/4.50    inference(cnf_transformation,[],[f15])).
% 31.51/4.50  
% 31.51/4.50  fof(f79,plain,(
% 31.51/4.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))),
% 31.51/4.50    inference(definition_unfolding,[],[f71,f62])).
% 31.51/4.50  
% 31.51/4.50  fof(f69,plain,(
% 31.51/4.50    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 31.51/4.50    inference(cnf_transformation,[],[f44])).
% 31.51/4.50  
% 31.51/4.50  fof(f81,plain,(
% 31.51/4.50    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 31.51/4.50    inference(definition_unfolding,[],[f69,f62])).
% 31.51/4.50  
% 31.51/4.50  fof(f70,plain,(
% 31.51/4.50    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 31.51/4.50    inference(cnf_transformation,[],[f44])).
% 31.51/4.50  
% 31.51/4.50  fof(f80,plain,(
% 31.51/4.50    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 31.51/4.50    inference(definition_unfolding,[],[f70,f62])).
% 31.51/4.50  
% 31.51/4.50  fof(f17,axiom,(
% 31.51/4.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f30,plain,(
% 31.51/4.50    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 31.51/4.50    inference(ennf_transformation,[],[f17])).
% 31.51/4.50  
% 31.51/4.50  fof(f31,plain,(
% 31.51/4.50    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 31.51/4.50    inference(flattening,[],[f30])).
% 31.51/4.50  
% 31.51/4.50  fof(f64,plain,(
% 31.51/4.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 31.51/4.50    inference(cnf_transformation,[],[f31])).
% 31.51/4.50  
% 31.51/4.50  fof(f78,plain,(
% 31.51/4.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 31.51/4.50    inference(definition_unfolding,[],[f64,f62,f62,f62,f62])).
% 31.51/4.50  
% 31.51/4.50  fof(f68,plain,(
% 31.51/4.50    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))),
% 31.51/4.50    inference(cnf_transformation,[],[f44])).
% 31.51/4.50  
% 31.51/4.50  fof(f82,plain,(
% 31.51/4.50    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))),
% 31.51/4.50    inference(definition_unfolding,[],[f68,f62])).
% 31.51/4.50  
% 31.51/4.50  fof(f67,plain,(
% 31.51/4.50    ~v1_xboole_0(sK4)),
% 31.51/4.50    inference(cnf_transformation,[],[f44])).
% 31.51/4.50  
% 31.51/4.50  fof(f14,axiom,(
% 31.51/4.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f26,plain,(
% 31.51/4.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 31.51/4.50    inference(ennf_transformation,[],[f14])).
% 31.51/4.50  
% 31.51/4.50  fof(f27,plain,(
% 31.51/4.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 31.51/4.50    inference(flattening,[],[f26])).
% 31.51/4.50  
% 31.51/4.50  fof(f61,plain,(
% 31.51/4.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 31.51/4.50    inference(cnf_transformation,[],[f27])).
% 31.51/4.50  
% 31.51/4.50  fof(f65,plain,(
% 31.51/4.50    ~v2_struct_0(sK3)),
% 31.51/4.50    inference(cnf_transformation,[],[f44])).
% 31.51/4.50  
% 31.51/4.50  fof(f66,plain,(
% 31.51/4.50    l1_struct_0(sK3)),
% 31.51/4.50    inference(cnf_transformation,[],[f44])).
% 31.51/4.50  
% 31.51/4.50  fof(f13,axiom,(
% 31.51/4.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f25,plain,(
% 31.51/4.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 31.51/4.50    inference(ennf_transformation,[],[f13])).
% 31.51/4.50  
% 31.51/4.50  fof(f60,plain,(
% 31.51/4.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 31.51/4.50    inference(cnf_transformation,[],[f25])).
% 31.51/4.50  
% 31.51/4.50  fof(f8,axiom,(
% 31.51/4.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f54,plain,(
% 31.51/4.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 31.51/4.50    inference(cnf_transformation,[],[f8])).
% 31.51/4.50  
% 31.51/4.50  fof(f4,axiom,(
% 31.51/4.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f50,plain,(
% 31.51/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.51/4.50    inference(cnf_transformation,[],[f4])).
% 31.51/4.50  
% 31.51/4.50  fof(f73,plain,(
% 31.51/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 31.51/4.50    inference(definition_unfolding,[],[f50,f52])).
% 31.51/4.50  
% 31.51/4.50  fof(f7,axiom,(
% 31.51/4.50    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f53,plain,(
% 31.51/4.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 31.51/4.50    inference(cnf_transformation,[],[f7])).
% 31.51/4.50  
% 31.51/4.50  fof(f5,axiom,(
% 31.51/4.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f51,plain,(
% 31.51/4.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.51/4.50    inference(cnf_transformation,[],[f5])).
% 31.51/4.50  
% 31.51/4.50  fof(f10,axiom,(
% 31.51/4.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f23,plain,(
% 31.51/4.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.51/4.50    inference(ennf_transformation,[],[f10])).
% 31.51/4.50  
% 31.51/4.50  fof(f56,plain,(
% 31.51/4.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.51/4.50    inference(cnf_transformation,[],[f23])).
% 31.51/4.50  
% 31.51/4.50  fof(f16,axiom,(
% 31.51/4.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 31.51/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.51/4.50  
% 31.51/4.50  fof(f28,plain,(
% 31.51/4.50    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 31.51/4.50    inference(ennf_transformation,[],[f16])).
% 31.51/4.50  
% 31.51/4.50  fof(f29,plain,(
% 31.51/4.50    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 31.51/4.50    inference(flattening,[],[f28])).
% 31.51/4.50  
% 31.51/4.50  fof(f63,plain,(
% 31.51/4.50    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 31.51/4.50    inference(cnf_transformation,[],[f29])).
% 31.51/4.50  
% 31.51/4.50  fof(f77,plain,(
% 31.51/4.50    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 31.51/4.50    inference(definition_unfolding,[],[f63,f62,f62,f62,f62])).
% 31.51/4.50  
% 31.51/4.50  fof(f72,plain,(
% 31.51/4.50    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4),
% 31.51/4.50    inference(cnf_transformation,[],[f44])).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3,plain,
% 31.51/4.50      ( v1_xboole_0(k1_xboole_0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f47]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_32865,plain,
% 31.51/4.50      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_9,plain,
% 31.51/4.50      ( r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 31.51/4.50      inference(cnf_transformation,[],[f55]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_32862,plain,
% 31.51/4.50      ( r1_xboole_0(k1_tarski(X0),X1) = iProver_top
% 31.51/4.50      | r2_hidden(X0,X1) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_13,plain,
% 31.51/4.50      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 31.51/4.50      inference(cnf_transformation,[],[f58]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_32860,plain,
% 31.51/4.50      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_4,negated_conjecture,
% 31.51/4.50      ( ~ r1_xboole_0(X0,X1)
% 31.51/4.50      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 31.51/4.50      inference(cnf_transformation,[],[f74]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_32864,plain,
% 31.51/4.50      ( r1_xboole_0(X0,X1) != iProver_top
% 31.51/4.50      | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_11,plain,
% 31.51/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 31.51/4.50      inference(cnf_transformation,[],[f76]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_32940,plain,
% 31.51/4.50      ( r1_xboole_0(X0,X1) != iProver_top
% 31.51/4.50      | r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_32864,c_11]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33167,plain,
% 31.51/4.50      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 31.51/4.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_32860,c_32940]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33994,plain,
% 31.51/4.50      ( k1_setfam_1(k2_tarski(k1_tarski(X0),X1)) = k1_xboole_0
% 31.51/4.50      | r2_hidden(X0,X1) = iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_32862,c_33167]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_19,negated_conjecture,
% 31.51/4.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
% 31.51/4.50      inference(cnf_transformation,[],[f79]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_21,negated_conjecture,
% 31.51/4.50      ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 31.51/4.50      inference(cnf_transformation,[],[f81]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_20,negated_conjecture,
% 31.51/4.50      ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 31.51/4.50      inference(cnf_transformation,[],[f80]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_17,plain,
% 31.51/4.50      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 31.51/4.50      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 31.51/4.50      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 31.51/4.50      | ~ r2_hidden(X2,X0)
% 31.51/4.50      | ~ v1_xboole_0(X2)
% 31.51/4.50      | v1_xboole_0(X1)
% 31.51/4.50      | v1_xboole_0(X0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f78]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_22,negated_conjecture,
% 31.51/4.50      ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
% 31.51/4.50      inference(cnf_transformation,[],[f82]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_287,plain,
% 31.51/4.50      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 31.51/4.50      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 31.51/4.50      | ~ r2_hidden(X2,X0)
% 31.51/4.50      | ~ v1_xboole_0(X2)
% 31.51/4.50      | v1_xboole_0(X0)
% 31.51/4.50      | v1_xboole_0(X1)
% 31.51/4.50      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 31.51/4.50      | sK4 != X0 ),
% 31.51/4.50      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_288,plain,
% 31.51/4.50      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 31.51/4.50      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 31.51/4.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 31.51/4.50      | ~ r2_hidden(X1,sK4)
% 31.51/4.50      | ~ v1_xboole_0(X1)
% 31.51/4.50      | v1_xboole_0(X0)
% 31.51/4.50      | v1_xboole_0(sK4)
% 31.51/4.50      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 31.51/4.50      inference(unflattening,[status(thm)],[c_287]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_23,negated_conjecture,
% 31.51/4.50      ( ~ v1_xboole_0(sK4) ),
% 31.51/4.50      inference(cnf_transformation,[],[f67]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_290,plain,
% 31.51/4.50      ( v1_xboole_0(X0)
% 31.51/4.50      | ~ v1_xboole_0(X1)
% 31.51/4.50      | ~ r2_hidden(X1,sK4)
% 31.51/4.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 31.51/4.50      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 31.51/4.50      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 31.51/4.50      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_288,c_23]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_291,plain,
% 31.51/4.50      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 31.51/4.50      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 31.51/4.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 31.51/4.50      | ~ r2_hidden(X1,sK4)
% 31.51/4.50      | ~ v1_xboole_0(X1)
% 31.51/4.50      | v1_xboole_0(X0)
% 31.51/4.50      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 31.51/4.50      inference(renaming,[status(thm)],[c_290]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_376,plain,
% 31.51/4.50      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 31.51/4.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 31.51/4.50      | ~ r2_hidden(X1,sK4)
% 31.51/4.50      | ~ v1_xboole_0(X1)
% 31.51/4.50      | v1_xboole_0(X0)
% 31.51/4.50      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 31.51/4.50      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 31.51/4.50      | sK4 != sK4 ),
% 31.51/4.50      inference(resolution_lifted,[status(thm)],[c_20,c_291]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_421,plain,
% 31.51/4.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 31.51/4.50      | ~ r2_hidden(X1,sK4)
% 31.51/4.50      | ~ v1_xboole_0(X1)
% 31.51/4.50      | v1_xboole_0(X0)
% 31.51/4.50      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 31.51/4.50      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 31.51/4.50      | sK4 != sK4 ),
% 31.51/4.50      inference(resolution_lifted,[status(thm)],[c_21,c_376]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_462,plain,
% 31.51/4.50      ( ~ r2_hidden(X0,sK4)
% 31.51/4.50      | ~ v1_xboole_0(X0)
% 31.51/4.50      | v1_xboole_0(X1)
% 31.51/4.50      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 31.51/4.50      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 31.51/4.50      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 31.51/4.50      | sK4 != sK4 ),
% 31.51/4.50      inference(resolution_lifted,[status(thm)],[c_19,c_421]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_732,plain,
% 31.51/4.50      ( ~ r2_hidden(X0,sK4)
% 31.51/4.50      | ~ v1_xboole_0(X0)
% 31.51/4.50      | v1_xboole_0(X1)
% 31.51/4.50      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 31.51/4.50      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 31.51/4.50      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
% 31.51/4.50      inference(equality_resolution_simp,[status(thm)],[c_462]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1054,plain,
% 31.51/4.50      ( ~ r2_hidden(X0,sK4) | ~ v1_xboole_0(X0) | ~ sP1_iProver_split ),
% 31.51/4.50      inference(splitting,
% 31.51/4.50                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 31.51/4.50                [c_732]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_32853,plain,
% 31.51/4.50      ( r2_hidden(X0,sK4) != iProver_top
% 31.51/4.50      | v1_xboole_0(X0) != iProver_top
% 31.51/4.50      | sP1_iProver_split != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_1054]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_34361,plain,
% 31.51/4.50      ( k1_setfam_1(k2_tarski(k1_tarski(X0),sK4)) = k1_xboole_0
% 31.51/4.50      | v1_xboole_0(X0) != iProver_top
% 31.51/4.50      | sP1_iProver_split != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_33994,c_32853]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1055,plain,
% 31.51/4.50      ( sP1_iProver_split | sP0_iProver_split ),
% 31.51/4.50      inference(splitting,
% 31.51/4.50                [splitting(split),new_symbols(definition,[])],
% 31.51/4.50                [c_732]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1091,plain,
% 31.51/4.50      ( sP1_iProver_split = iProver_top
% 31.51/4.50      | sP0_iProver_split = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_1055]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_15,plain,
% 31.51/4.50      ( v2_struct_0(X0)
% 31.51/4.50      | ~ l1_struct_0(X0)
% 31.51/4.50      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 31.51/4.50      inference(cnf_transformation,[],[f61]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_25,negated_conjecture,
% 31.51/4.50      ( ~ v2_struct_0(sK3) ),
% 31.51/4.50      inference(cnf_transformation,[],[f65]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_324,plain,
% 31.51/4.50      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 31.51/4.50      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_325,plain,
% 31.51/4.50      ( ~ l1_struct_0(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 31.51/4.50      inference(unflattening,[status(thm)],[c_324]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_24,negated_conjecture,
% 31.51/4.50      ( l1_struct_0(sK3) ),
% 31.51/4.50      inference(cnf_transformation,[],[f66]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_44,plain,
% 31.51/4.50      ( v2_struct_0(sK3)
% 31.51/4.50      | ~ l1_struct_0(sK3)
% 31.51/4.50      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_15]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_327,plain,
% 31.51/4.50      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_325,c_25,c_24,c_44]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_32855,plain,
% 31.51/4.50      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_14,plain,
% 31.51/4.50      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f60]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_370,plain,
% 31.51/4.50      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 31.51/4.50      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_371,plain,
% 31.51/4.50      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 31.51/4.50      inference(unflattening,[status(thm)],[c_370]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_32878,plain,
% 31.51/4.50      ( v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_32855,c_371]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1053,plain,
% 31.51/4.50      ( v1_xboole_0(X0)
% 31.51/4.50      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 31.51/4.50      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 31.51/4.50      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 31.51/4.50      | ~ sP0_iProver_split ),
% 31.51/4.50      inference(splitting,
% 31.51/4.50                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 31.51/4.50                [c_732]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_32854,plain,
% 31.51/4.50      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 31.51/4.50      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 31.51/4.50      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 31.51/4.50      | v1_xboole_0(X0) = iProver_top
% 31.51/4.50      | sP0_iProver_split != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_1053]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33139,plain,
% 31.51/4.50      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 31.51/4.50      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 31.51/4.50      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 31.51/4.50      | sP0_iProver_split != iProver_top ),
% 31.51/4.50      inference(equality_resolution,[status(thm)],[c_32854]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33144,plain,
% 31.51/4.50      ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 31.51/4.50      | sP0_iProver_split != iProver_top ),
% 31.51/4.50      inference(equality_resolution_simp,[status(thm)],[c_33139]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_36083,plain,
% 31.51/4.50      ( v1_xboole_0(X0) != iProver_top
% 31.51/4.50      | k1_setfam_1(k2_tarski(k1_tarski(X0),sK4)) = k1_xboole_0 ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_34361,c_1091,c_32878,c_33144]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_36084,plain,
% 31.51/4.50      ( k1_setfam_1(k2_tarski(k1_tarski(X0),sK4)) = k1_xboole_0
% 31.51/4.50      | v1_xboole_0(X0) != iProver_top ),
% 31.51/4.50      inference(renaming,[status(thm)],[c_36083]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_36091,plain,
% 31.51/4.50      ( k1_setfam_1(k2_tarski(k1_tarski(k1_xboole_0),sK4)) = k1_xboole_0 ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_32865,c_36084]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_8,plain,
% 31.51/4.50      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f54]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_0,plain,
% 31.51/4.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 31.51/4.50      inference(cnf_transformation,[],[f73]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_32910,plain,
% 31.51/4.50      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_0,c_11]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33582,plain,
% 31.51/4.50      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_8,c_32910]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_129024,plain,
% 31.51/4.50      ( k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) = k5_xboole_0(sK4,k1_xboole_0) ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_36091,c_33582]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_7,plain,
% 31.51/4.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.51/4.50      inference(cnf_transformation,[],[f53]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33098,plain,
% 31.51/4.50      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_11,c_7]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33225,plain,
% 31.51/4.50      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_8,c_33098]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33580,plain,
% 31.51/4.50      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_33225,c_32910]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_6,plain,
% 31.51/4.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.51/4.50      inference(cnf_transformation,[],[f51]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33590,plain,
% 31.51/4.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_33580,c_6]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_129075,plain,
% 31.51/4.50      ( k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) = sK4 ),
% 31.51/4.50      inference(demodulation,[status(thm)],[c_129024,c_33590]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_10,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.51/4.50      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 31.51/4.50      inference(cnf_transformation,[],[f56]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_453,plain,
% 31.51/4.50      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 31.51/4.50      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X0)
% 31.51/4.50      | sK4 != X1 ),
% 31.51/4.50      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_454,plain,
% 31.51/4.50      ( k7_subset_1(X0,sK4,X1) = k4_xboole_0(sK4,X1)
% 31.51/4.50      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X0) ),
% 31.51/4.50      inference(unflattening,[status(thm)],[c_453]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33021,plain,
% 31.51/4.50      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,X0) = k4_xboole_0(sK4,X0) ),
% 31.51/4.50      inference(equality_resolution,[status(thm)],[c_454]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_16,plain,
% 31.51/4.50      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 31.51/4.50      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 31.51/4.50      | v2_struct_0(X1)
% 31.51/4.50      | ~ l1_struct_0(X1)
% 31.51/4.50      | v1_xboole_0(X0)
% 31.51/4.50      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
% 31.51/4.50      inference(cnf_transformation,[],[f77]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_335,plain,
% 31.51/4.50      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 31.51/4.50      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 31.51/4.50      | ~ l1_struct_0(X1)
% 31.51/4.50      | v1_xboole_0(X0)
% 31.51/4.50      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
% 31.51/4.50      | sK3 != X1 ),
% 31.51/4.50      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_336,plain,
% 31.51/4.50      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 31.51/4.50      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 31.51/4.50      | ~ l1_struct_0(sK3)
% 31.51/4.50      | v1_xboole_0(X0)
% 31.51/4.50      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 31.51/4.50      inference(unflattening,[status(thm)],[c_335]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_340,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 31.51/4.50      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 31.51/4.50      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 31.51/4.50      | v1_xboole_0(X0)
% 31.51/4.50      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_336,c_24]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_341,plain,
% 31.51/4.50      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 31.51/4.50      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 31.51/4.50      | v1_xboole_0(X0)
% 31.51/4.50      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 31.51/4.50      inference(renaming,[status(thm)],[c_340]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_403,plain,
% 31.51/4.50      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 31.51/4.50      | v1_xboole_0(X0)
% 31.51/4.50      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
% 31.51/4.50      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 31.51/4.50      | sK4 != X0 ),
% 31.51/4.50      inference(resolution_lifted,[status(thm)],[c_20,c_341]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_404,plain,
% 31.51/4.50      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 31.51/4.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 31.51/4.50      | v1_xboole_0(sK4)
% 31.51/4.50      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 31.51/4.50      inference(unflattening,[status(thm)],[c_403]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_406,plain,
% 31.51/4.50      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_404,c_23,c_21,c_19]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33053,plain,
% 31.51/4.50      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) ),
% 31.51/4.50      inference(demodulation,[status(thm)],[c_33021,c_406]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_18,negated_conjecture,
% 31.51/4.50      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
% 31.51/4.50      inference(cnf_transformation,[],[f72]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33111,plain,
% 31.51/4.50      ( k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) != sK4 ),
% 31.51/4.50      inference(demodulation,[status(thm)],[c_33053,c_18]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(contradiction,plain,
% 31.51/4.50      ( $false ),
% 31.51/4.50      inference(minisat,[status(thm)],[c_129075,c_33111]) ).
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.51/4.50  
% 31.51/4.50  ------                               Statistics
% 31.51/4.50  
% 31.51/4.50  ------ Selected
% 31.51/4.50  
% 31.51/4.50  total_time:                             3.874
% 31.51/4.50  
%------------------------------------------------------------------------------
