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
% DateTime   : Thu Dec  3 12:29:04 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 675 expanded)
%              Number of clauses        :   76 ( 125 expanded)
%              Number of leaves         :   27 ( 202 expanded)
%              Depth                    :   24
%              Number of atoms          :  508 (2932 expanded)
%              Number of equality atoms :  168 ( 680 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f82])).

fof(f15,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f19,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f18,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f71,f70])).

fof(f87,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f67,f86])).

fof(f92,plain,(
    k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0))) ),
    inference(definition_unfolding,[],[f61,f85,f87])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f85])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f90,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f56,f82,f82])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f42])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f63,f82])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f53,f83])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f44])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f48,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
    & ~ v1_xboole_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f47,f46])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f48])).

fof(f96,plain,(
    m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))))) ),
    inference(definition_unfolding,[],[f80,f87,f70])).

fof(f78,plain,(
    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,(
    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f78,f70])).

fof(f79,plain,(
    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f48])).

fof(f97,plain,(
    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f79,f70])).

fof(f21,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f73,f87,f70,f70,f70,f70])).

fof(f77,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f99,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(definition_unfolding,[],[f77,f70])).

fof(f76,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f20,axiom,(
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

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f72,f70,f85,f87,f70,f70,f70])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f83])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f62,f84,f87])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f81,plain,(
    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_8,plain,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_7,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1537,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2309,plain,
    ( r1_xboole_0(u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0))),X0) = iProver_top
    | r2_hidden(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1537])).

cnf(c_6,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1542,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1539,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2582,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_1539])).

cnf(c_2764,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2582])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1534,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1541,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2181,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1534,c_1541])).

cnf(c_2918,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2764,c_2181])).

cnf(c_3165,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0))))) = k1_xboole_0
    | r2_hidden(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2309,c_2918])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_20,negated_conjecture,
    ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_19,negated_conjecture,
    ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_16,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_21,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_272,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_273,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_275,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_22])).

cnf(c_276,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_357,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_276])).

cnf(c_402,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_357])).

cnf(c_443,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_402])).

cnf(c_832,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_443])).

cnf(c_1246,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_832])).

cnf(c_1530,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1246])).

cnf(c_3389,plain,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0))))) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3165,c_1530])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_26,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_63,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_309,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_310,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_311,plain,
    ( l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_1247,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_832])).

cnf(c_1278,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1247])).

cnf(c_1245,plain,
    ( v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_832])).

cnf(c_1531,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_351,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_352,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_1614,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(u1_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1531,c_352])).

cnf(c_1732,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))
    | k3_lattice3(k1_lattice3(u1_struct_0(sK3))) != k3_lattice3(k1_lattice3(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1614])).

cnf(c_2033,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1732])).

cnf(c_3424,plain,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0))))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3389,c_26,c_63,c_311,c_1278,c_2033])).

cnf(c_15,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_320,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_321,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | ~ l1_struct_0(sK3)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_323,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_23])).

cnf(c_324,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(renaming,[status(thm)],[c_323])).

cnf(c_384,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_324])).

cnf(c_385,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | v1_xboole_0(sK4)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_387,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_22,c_20,c_18])).

cnf(c_1594,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))),sK4,u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0)))) = k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) ),
    inference(light_normalisation,[status(thm)],[c_387,c_8,c_352])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_434,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X2)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_435,plain,
    ( k5_xboole_0(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,X0))) = k7_subset_1(X1,sK4,X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X1))) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_1609,plain,
    ( k5_xboole_0(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,X0))) = k7_subset_1(X1,sK4,X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X1))) ),
    inference(light_normalisation,[status(thm)],[c_435,c_352])).

cnf(c_1701,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))),sK4,X0) = k5_xboole_0(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,X0))) ),
    inference(equality_resolution,[status(thm)],[c_1609])).

cnf(c_1997,plain,
    ( k5_xboole_0(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0)))))) = k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) ),
    inference(superposition,[status(thm)],[c_1594,c_1701])).

cnf(c_3427,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) = k5_xboole_0(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3424,c_1997])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3428,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) = sK4 ),
    inference(demodulation,[status(thm)],[c_3427,c_5])).

cnf(c_17,negated_conjecture,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1557,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) != sK4 ),
    inference(light_normalisation,[status(thm)],[c_17,c_352])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3428,c_1557])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:44:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.03/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.03/0.99  
% 2.03/0.99  ------  iProver source info
% 2.03/0.99  
% 2.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.03/0.99  git: non_committed_changes: false
% 2.03/0.99  git: last_make_outside_of_git: false
% 2.03/0.99  
% 2.03/0.99  ------ 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options
% 2.03/0.99  
% 2.03/0.99  --out_options                           all
% 2.03/0.99  --tptp_safe_out                         true
% 2.03/0.99  --problem_path                          ""
% 2.03/0.99  --include_path                          ""
% 2.03/0.99  --clausifier                            res/vclausify_rel
% 2.03/0.99  --clausifier_options                    --mode clausify
% 2.03/0.99  --stdin                                 false
% 2.03/0.99  --stats_out                             all
% 2.03/0.99  
% 2.03/0.99  ------ General Options
% 2.03/0.99  
% 2.03/0.99  --fof                                   false
% 2.03/0.99  --time_out_real                         305.
% 2.03/0.99  --time_out_virtual                      -1.
% 2.03/0.99  --symbol_type_check                     false
% 2.03/0.99  --clausify_out                          false
% 2.03/0.99  --sig_cnt_out                           false
% 2.03/0.99  --trig_cnt_out                          false
% 2.03/0.99  --trig_cnt_out_tolerance                1.
% 2.03/0.99  --trig_cnt_out_sk_spl                   false
% 2.03/0.99  --abstr_cl_out                          false
% 2.03/0.99  
% 2.03/0.99  ------ Global Options
% 2.03/0.99  
% 2.03/0.99  --schedule                              default
% 2.03/0.99  --add_important_lit                     false
% 2.03/0.99  --prop_solver_per_cl                    1000
% 2.03/0.99  --min_unsat_core                        false
% 2.03/0.99  --soft_assumptions                      false
% 2.03/0.99  --soft_lemma_size                       3
% 2.03/0.99  --prop_impl_unit_size                   0
% 2.03/0.99  --prop_impl_unit                        []
% 2.03/0.99  --share_sel_clauses                     true
% 2.03/0.99  --reset_solvers                         false
% 2.03/0.99  --bc_imp_inh                            [conj_cone]
% 2.03/0.99  --conj_cone_tolerance                   3.
% 2.03/0.99  --extra_neg_conj                        none
% 2.03/0.99  --large_theory_mode                     true
% 2.03/0.99  --prolific_symb_bound                   200
% 2.03/0.99  --lt_threshold                          2000
% 2.03/0.99  --clause_weak_htbl                      true
% 2.03/0.99  --gc_record_bc_elim                     false
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing Options
% 2.03/0.99  
% 2.03/0.99  --preprocessing_flag                    true
% 2.03/0.99  --time_out_prep_mult                    0.1
% 2.03/0.99  --splitting_mode                        input
% 2.03/0.99  --splitting_grd                         true
% 2.03/0.99  --splitting_cvd                         false
% 2.03/0.99  --splitting_cvd_svl                     false
% 2.03/0.99  --splitting_nvd                         32
% 2.03/0.99  --sub_typing                            true
% 2.03/0.99  --prep_gs_sim                           true
% 2.03/0.99  --prep_unflatten                        true
% 2.03/0.99  --prep_res_sim                          true
% 2.03/0.99  --prep_upred                            true
% 2.03/0.99  --prep_sem_filter                       exhaustive
% 2.03/0.99  --prep_sem_filter_out                   false
% 2.03/0.99  --pred_elim                             true
% 2.03/0.99  --res_sim_input                         true
% 2.03/0.99  --eq_ax_congr_red                       true
% 2.03/0.99  --pure_diseq_elim                       true
% 2.03/0.99  --brand_transform                       false
% 2.03/0.99  --non_eq_to_eq                          false
% 2.03/0.99  --prep_def_merge                        true
% 2.03/0.99  --prep_def_merge_prop_impl              false
% 2.03/0.99  --prep_def_merge_mbd                    true
% 2.03/0.99  --prep_def_merge_tr_red                 false
% 2.03/0.99  --prep_def_merge_tr_cl                  false
% 2.03/0.99  --smt_preprocessing                     true
% 2.03/0.99  --smt_ac_axioms                         fast
% 2.03/0.99  --preprocessed_out                      false
% 2.03/0.99  --preprocessed_stats                    false
% 2.03/0.99  
% 2.03/0.99  ------ Abstraction refinement Options
% 2.03/0.99  
% 2.03/0.99  --abstr_ref                             []
% 2.03/0.99  --abstr_ref_prep                        false
% 2.03/0.99  --abstr_ref_until_sat                   false
% 2.03/0.99  --abstr_ref_sig_restrict                funpre
% 2.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.99  --abstr_ref_under                       []
% 2.03/0.99  
% 2.03/0.99  ------ SAT Options
% 2.03/0.99  
% 2.03/0.99  --sat_mode                              false
% 2.03/0.99  --sat_fm_restart_options                ""
% 2.03/0.99  --sat_gr_def                            false
% 2.03/0.99  --sat_epr_types                         true
% 2.03/0.99  --sat_non_cyclic_types                  false
% 2.03/0.99  --sat_finite_models                     false
% 2.03/0.99  --sat_fm_lemmas                         false
% 2.03/0.99  --sat_fm_prep                           false
% 2.03/0.99  --sat_fm_uc_incr                        true
% 2.03/0.99  --sat_out_model                         small
% 2.03/0.99  --sat_out_clauses                       false
% 2.03/0.99  
% 2.03/0.99  ------ QBF Options
% 2.03/0.99  
% 2.03/0.99  --qbf_mode                              false
% 2.03/0.99  --qbf_elim_univ                         false
% 2.03/0.99  --qbf_dom_inst                          none
% 2.03/0.99  --qbf_dom_pre_inst                      false
% 2.03/0.99  --qbf_sk_in                             false
% 2.03/0.99  --qbf_pred_elim                         true
% 2.03/0.99  --qbf_split                             512
% 2.03/0.99  
% 2.03/0.99  ------ BMC1 Options
% 2.03/0.99  
% 2.03/0.99  --bmc1_incremental                      false
% 2.03/0.99  --bmc1_axioms                           reachable_all
% 2.03/0.99  --bmc1_min_bound                        0
% 2.03/0.99  --bmc1_max_bound                        -1
% 2.03/0.99  --bmc1_max_bound_default                -1
% 2.03/0.99  --bmc1_symbol_reachability              true
% 2.03/0.99  --bmc1_property_lemmas                  false
% 2.03/0.99  --bmc1_k_induction                      false
% 2.03/0.99  --bmc1_non_equiv_states                 false
% 2.03/0.99  --bmc1_deadlock                         false
% 2.03/0.99  --bmc1_ucm                              false
% 2.03/0.99  --bmc1_add_unsat_core                   none
% 2.03/0.99  --bmc1_unsat_core_children              false
% 2.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.99  --bmc1_out_stat                         full
% 2.03/0.99  --bmc1_ground_init                      false
% 2.03/0.99  --bmc1_pre_inst_next_state              false
% 2.03/0.99  --bmc1_pre_inst_state                   false
% 2.03/0.99  --bmc1_pre_inst_reach_state             false
% 2.03/0.99  --bmc1_out_unsat_core                   false
% 2.03/0.99  --bmc1_aig_witness_out                  false
% 2.03/0.99  --bmc1_verbose                          false
% 2.03/0.99  --bmc1_dump_clauses_tptp                false
% 2.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.99  --bmc1_dump_file                        -
% 2.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.99  --bmc1_ucm_extend_mode                  1
% 2.03/0.99  --bmc1_ucm_init_mode                    2
% 2.03/0.99  --bmc1_ucm_cone_mode                    none
% 2.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.99  --bmc1_ucm_relax_model                  4
% 2.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.99  --bmc1_ucm_layered_model                none
% 2.03/0.99  --bmc1_ucm_max_lemma_size               10
% 2.03/0.99  
% 2.03/0.99  ------ AIG Options
% 2.03/0.99  
% 2.03/0.99  --aig_mode                              false
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation Options
% 2.03/0.99  
% 2.03/0.99  --instantiation_flag                    true
% 2.03/0.99  --inst_sos_flag                         false
% 2.03/0.99  --inst_sos_phase                        true
% 2.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel_side                     num_symb
% 2.03/0.99  --inst_solver_per_active                1400
% 2.03/0.99  --inst_solver_calls_frac                1.
% 2.03/0.99  --inst_passive_queue_type               priority_queues
% 2.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.99  --inst_passive_queues_freq              [25;2]
% 2.03/0.99  --inst_dismatching                      true
% 2.03/0.99  --inst_eager_unprocessed_to_passive     true
% 2.03/0.99  --inst_prop_sim_given                   true
% 2.03/0.99  --inst_prop_sim_new                     false
% 2.03/0.99  --inst_subs_new                         false
% 2.03/0.99  --inst_eq_res_simp                      false
% 2.03/0.99  --inst_subs_given                       false
% 2.03/0.99  --inst_orphan_elimination               true
% 2.03/0.99  --inst_learning_loop_flag               true
% 2.03/0.99  --inst_learning_start                   3000
% 2.03/0.99  --inst_learning_factor                  2
% 2.03/0.99  --inst_start_prop_sim_after_learn       3
% 2.03/0.99  --inst_sel_renew                        solver
% 2.03/0.99  --inst_lit_activity_flag                true
% 2.03/0.99  --inst_restr_to_given                   false
% 2.03/0.99  --inst_activity_threshold               500
% 2.03/0.99  --inst_out_proof                        true
% 2.03/0.99  
% 2.03/0.99  ------ Resolution Options
% 2.03/0.99  
% 2.03/0.99  --resolution_flag                       true
% 2.03/0.99  --res_lit_sel                           adaptive
% 2.03/0.99  --res_lit_sel_side                      none
% 2.03/0.99  --res_ordering                          kbo
% 2.03/0.99  --res_to_prop_solver                    active
% 2.03/0.99  --res_prop_simpl_new                    false
% 2.03/0.99  --res_prop_simpl_given                  true
% 2.03/0.99  --res_passive_queue_type                priority_queues
% 2.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.99  --res_passive_queues_freq               [15;5]
% 2.03/0.99  --res_forward_subs                      full
% 2.03/0.99  --res_backward_subs                     full
% 2.03/0.99  --res_forward_subs_resolution           true
% 2.03/0.99  --res_backward_subs_resolution          true
% 2.03/0.99  --res_orphan_elimination                true
% 2.03/0.99  --res_time_limit                        2.
% 2.03/0.99  --res_out_proof                         true
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Options
% 2.03/0.99  
% 2.03/0.99  --superposition_flag                    true
% 2.03/0.99  --sup_passive_queue_type                priority_queues
% 2.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.99  --demod_completeness_check              fast
% 2.03/0.99  --demod_use_ground                      true
% 2.03/0.99  --sup_to_prop_solver                    passive
% 2.03/0.99  --sup_prop_simpl_new                    true
% 2.03/0.99  --sup_prop_simpl_given                  true
% 2.03/0.99  --sup_fun_splitting                     false
% 2.03/0.99  --sup_smt_interval                      50000
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Simplification Setup
% 2.03/0.99  
% 2.03/0.99  --sup_indices_passive                   []
% 2.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_full_bw                           [BwDemod]
% 2.03/0.99  --sup_immed_triv                        [TrivRules]
% 2.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_immed_bw_main                     []
% 2.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  
% 2.03/0.99  ------ Combination Options
% 2.03/0.99  
% 2.03/0.99  --comb_res_mult                         3
% 2.03/0.99  --comb_sup_mult                         2
% 2.03/0.99  --comb_inst_mult                        10
% 2.03/0.99  
% 2.03/0.99  ------ Debug Options
% 2.03/0.99  
% 2.03/0.99  --dbg_backtrace                         false
% 2.03/0.99  --dbg_dump_prop_clauses                 false
% 2.03/0.99  --dbg_dump_prop_clauses_file            -
% 2.03/0.99  --dbg_out_stat                          false
% 2.03/0.99  ------ Parsing...
% 2.03/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.03/0.99  ------ Proving...
% 2.03/0.99  ------ Problem Properties 
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  clauses                                 21
% 2.03/0.99  conjectures                             2
% 2.03/0.99  EPR                                     5
% 2.03/0.99  Horn                                    16
% 2.03/0.99  unary                                   9
% 2.03/0.99  binary                                  8
% 2.03/0.99  lits                                    39
% 2.03/0.99  lits eq                                 16
% 2.03/0.99  fd_pure                                 0
% 2.03/0.99  fd_pseudo                               0
% 2.03/0.99  fd_cond                                 3
% 2.03/0.99  fd_pseudo_cond                          0
% 2.03/0.99  AC symbols                              0
% 2.03/0.99  
% 2.03/0.99  ------ Schedule dynamic 5 is on 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  ------ 
% 2.03/0.99  Current options:
% 2.03/0.99  ------ 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options
% 2.03/0.99  
% 2.03/0.99  --out_options                           all
% 2.03/0.99  --tptp_safe_out                         true
% 2.03/0.99  --problem_path                          ""
% 2.03/0.99  --include_path                          ""
% 2.03/0.99  --clausifier                            res/vclausify_rel
% 2.03/0.99  --clausifier_options                    --mode clausify
% 2.03/0.99  --stdin                                 false
% 2.03/0.99  --stats_out                             all
% 2.03/0.99  
% 2.03/0.99  ------ General Options
% 2.03/0.99  
% 2.03/0.99  --fof                                   false
% 2.03/0.99  --time_out_real                         305.
% 2.03/0.99  --time_out_virtual                      -1.
% 2.03/0.99  --symbol_type_check                     false
% 2.03/0.99  --clausify_out                          false
% 2.03/0.99  --sig_cnt_out                           false
% 2.03/0.99  --trig_cnt_out                          false
% 2.03/0.99  --trig_cnt_out_tolerance                1.
% 2.03/0.99  --trig_cnt_out_sk_spl                   false
% 2.03/0.99  --abstr_cl_out                          false
% 2.03/0.99  
% 2.03/0.99  ------ Global Options
% 2.03/0.99  
% 2.03/0.99  --schedule                              default
% 2.03/0.99  --add_important_lit                     false
% 2.03/0.99  --prop_solver_per_cl                    1000
% 2.03/0.99  --min_unsat_core                        false
% 2.03/0.99  --soft_assumptions                      false
% 2.03/0.99  --soft_lemma_size                       3
% 2.03/0.99  --prop_impl_unit_size                   0
% 2.03/0.99  --prop_impl_unit                        []
% 2.03/0.99  --share_sel_clauses                     true
% 2.03/0.99  --reset_solvers                         false
% 2.03/0.99  --bc_imp_inh                            [conj_cone]
% 2.03/0.99  --conj_cone_tolerance                   3.
% 2.03/0.99  --extra_neg_conj                        none
% 2.03/0.99  --large_theory_mode                     true
% 2.03/0.99  --prolific_symb_bound                   200
% 2.03/0.99  --lt_threshold                          2000
% 2.03/0.99  --clause_weak_htbl                      true
% 2.03/0.99  --gc_record_bc_elim                     false
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing Options
% 2.03/0.99  
% 2.03/0.99  --preprocessing_flag                    true
% 2.03/0.99  --time_out_prep_mult                    0.1
% 2.03/0.99  --splitting_mode                        input
% 2.03/0.99  --splitting_grd                         true
% 2.03/0.99  --splitting_cvd                         false
% 2.03/0.99  --splitting_cvd_svl                     false
% 2.03/0.99  --splitting_nvd                         32
% 2.03/0.99  --sub_typing                            true
% 2.03/0.99  --prep_gs_sim                           true
% 2.03/0.99  --prep_unflatten                        true
% 2.03/0.99  --prep_res_sim                          true
% 2.03/0.99  --prep_upred                            true
% 2.03/0.99  --prep_sem_filter                       exhaustive
% 2.03/0.99  --prep_sem_filter_out                   false
% 2.03/0.99  --pred_elim                             true
% 2.03/0.99  --res_sim_input                         true
% 2.03/0.99  --eq_ax_congr_red                       true
% 2.03/0.99  --pure_diseq_elim                       true
% 2.03/0.99  --brand_transform                       false
% 2.03/0.99  --non_eq_to_eq                          false
% 2.03/0.99  --prep_def_merge                        true
% 2.03/0.99  --prep_def_merge_prop_impl              false
% 2.03/0.99  --prep_def_merge_mbd                    true
% 2.03/0.99  --prep_def_merge_tr_red                 false
% 2.03/0.99  --prep_def_merge_tr_cl                  false
% 2.03/0.99  --smt_preprocessing                     true
% 2.03/0.99  --smt_ac_axioms                         fast
% 2.03/0.99  --preprocessed_out                      false
% 2.03/0.99  --preprocessed_stats                    false
% 2.03/0.99  
% 2.03/0.99  ------ Abstraction refinement Options
% 2.03/0.99  
% 2.03/0.99  --abstr_ref                             []
% 2.03/0.99  --abstr_ref_prep                        false
% 2.03/0.99  --abstr_ref_until_sat                   false
% 2.03/0.99  --abstr_ref_sig_restrict                funpre
% 2.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.99  --abstr_ref_under                       []
% 2.03/0.99  
% 2.03/0.99  ------ SAT Options
% 2.03/0.99  
% 2.03/0.99  --sat_mode                              false
% 2.03/0.99  --sat_fm_restart_options                ""
% 2.03/0.99  --sat_gr_def                            false
% 2.03/0.99  --sat_epr_types                         true
% 2.03/0.99  --sat_non_cyclic_types                  false
% 2.03/0.99  --sat_finite_models                     false
% 2.03/0.99  --sat_fm_lemmas                         false
% 2.03/0.99  --sat_fm_prep                           false
% 2.03/0.99  --sat_fm_uc_incr                        true
% 2.03/0.99  --sat_out_model                         small
% 2.03/0.99  --sat_out_clauses                       false
% 2.03/0.99  
% 2.03/0.99  ------ QBF Options
% 2.03/0.99  
% 2.03/0.99  --qbf_mode                              false
% 2.03/0.99  --qbf_elim_univ                         false
% 2.03/0.99  --qbf_dom_inst                          none
% 2.03/0.99  --qbf_dom_pre_inst                      false
% 2.03/0.99  --qbf_sk_in                             false
% 2.03/0.99  --qbf_pred_elim                         true
% 2.03/0.99  --qbf_split                             512
% 2.03/0.99  
% 2.03/0.99  ------ BMC1 Options
% 2.03/0.99  
% 2.03/0.99  --bmc1_incremental                      false
% 2.03/0.99  --bmc1_axioms                           reachable_all
% 2.03/0.99  --bmc1_min_bound                        0
% 2.03/0.99  --bmc1_max_bound                        -1
% 2.03/0.99  --bmc1_max_bound_default                -1
% 2.03/0.99  --bmc1_symbol_reachability              true
% 2.03/0.99  --bmc1_property_lemmas                  false
% 2.03/0.99  --bmc1_k_induction                      false
% 2.03/0.99  --bmc1_non_equiv_states                 false
% 2.03/0.99  --bmc1_deadlock                         false
% 2.03/0.99  --bmc1_ucm                              false
% 2.03/0.99  --bmc1_add_unsat_core                   none
% 2.03/0.99  --bmc1_unsat_core_children              false
% 2.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.99  --bmc1_out_stat                         full
% 2.03/0.99  --bmc1_ground_init                      false
% 2.03/0.99  --bmc1_pre_inst_next_state              false
% 2.03/0.99  --bmc1_pre_inst_state                   false
% 2.03/0.99  --bmc1_pre_inst_reach_state             false
% 2.03/0.99  --bmc1_out_unsat_core                   false
% 2.03/0.99  --bmc1_aig_witness_out                  false
% 2.03/0.99  --bmc1_verbose                          false
% 2.03/0.99  --bmc1_dump_clauses_tptp                false
% 2.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.99  --bmc1_dump_file                        -
% 2.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.99  --bmc1_ucm_extend_mode                  1
% 2.03/0.99  --bmc1_ucm_init_mode                    2
% 2.03/0.99  --bmc1_ucm_cone_mode                    none
% 2.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.99  --bmc1_ucm_relax_model                  4
% 2.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.99  --bmc1_ucm_layered_model                none
% 2.03/0.99  --bmc1_ucm_max_lemma_size               10
% 2.03/0.99  
% 2.03/0.99  ------ AIG Options
% 2.03/0.99  
% 2.03/0.99  --aig_mode                              false
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation Options
% 2.03/0.99  
% 2.03/0.99  --instantiation_flag                    true
% 2.03/0.99  --inst_sos_flag                         false
% 2.03/0.99  --inst_sos_phase                        true
% 2.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel_side                     none
% 2.03/0.99  --inst_solver_per_active                1400
% 2.03/0.99  --inst_solver_calls_frac                1.
% 2.03/0.99  --inst_passive_queue_type               priority_queues
% 2.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.99  --inst_passive_queues_freq              [25;2]
% 2.03/0.99  --inst_dismatching                      true
% 2.03/0.99  --inst_eager_unprocessed_to_passive     true
% 2.03/0.99  --inst_prop_sim_given                   true
% 2.03/0.99  --inst_prop_sim_new                     false
% 2.03/0.99  --inst_subs_new                         false
% 2.03/0.99  --inst_eq_res_simp                      false
% 2.03/0.99  --inst_subs_given                       false
% 2.03/0.99  --inst_orphan_elimination               true
% 2.03/0.99  --inst_learning_loop_flag               true
% 2.03/0.99  --inst_learning_start                   3000
% 2.03/0.99  --inst_learning_factor                  2
% 2.03/0.99  --inst_start_prop_sim_after_learn       3
% 2.03/0.99  --inst_sel_renew                        solver
% 2.03/0.99  --inst_lit_activity_flag                true
% 2.03/0.99  --inst_restr_to_given                   false
% 2.03/0.99  --inst_activity_threshold               500
% 2.03/0.99  --inst_out_proof                        true
% 2.03/0.99  
% 2.03/0.99  ------ Resolution Options
% 2.03/0.99  
% 2.03/0.99  --resolution_flag                       false
% 2.03/0.99  --res_lit_sel                           adaptive
% 2.03/0.99  --res_lit_sel_side                      none
% 2.03/0.99  --res_ordering                          kbo
% 2.03/0.99  --res_to_prop_solver                    active
% 2.03/0.99  --res_prop_simpl_new                    false
% 2.03/0.99  --res_prop_simpl_given                  true
% 2.03/0.99  --res_passive_queue_type                priority_queues
% 2.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.99  --res_passive_queues_freq               [15;5]
% 2.03/0.99  --res_forward_subs                      full
% 2.03/0.99  --res_backward_subs                     full
% 2.03/0.99  --res_forward_subs_resolution           true
% 2.03/0.99  --res_backward_subs_resolution          true
% 2.03/0.99  --res_orphan_elimination                true
% 2.03/0.99  --res_time_limit                        2.
% 2.03/0.99  --res_out_proof                         true
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Options
% 2.03/0.99  
% 2.03/0.99  --superposition_flag                    true
% 2.03/0.99  --sup_passive_queue_type                priority_queues
% 2.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.99  --demod_completeness_check              fast
% 2.03/0.99  --demod_use_ground                      true
% 2.03/0.99  --sup_to_prop_solver                    passive
% 2.03/0.99  --sup_prop_simpl_new                    true
% 2.03/0.99  --sup_prop_simpl_given                  true
% 2.03/0.99  --sup_fun_splitting                     false
% 2.03/0.99  --sup_smt_interval                      50000
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Simplification Setup
% 2.03/0.99  
% 2.03/0.99  --sup_indices_passive                   []
% 2.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_full_bw                           [BwDemod]
% 2.03/0.99  --sup_immed_triv                        [TrivRules]
% 2.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_immed_bw_main                     []
% 2.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  
% 2.03/0.99  ------ Combination Options
% 2.03/0.99  
% 2.03/0.99  --comb_res_mult                         3
% 2.03/0.99  --comb_sup_mult                         2
% 2.03/0.99  --comb_inst_mult                        10
% 2.03/0.99  
% 2.03/0.99  ------ Debug Options
% 2.03/0.99  
% 2.03/0.99  --dbg_backtrace                         false
% 2.03/0.99  --dbg_dump_prop_clauses                 false
% 2.03/0.99  --dbg_dump_prop_clauses_file            -
% 2.03/0.99  --dbg_out_stat                          false
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  ------ Proving...
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  % SZS status Theorem for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  fof(f11,axiom,(
% 2.03/0.99    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f61,plain,(
% 2.03/0.99    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 2.03/0.99    inference(cnf_transformation,[],[f11])).
% 2.03/0.99  
% 2.03/0.99  fof(f7,axiom,(
% 2.03/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f57,plain,(
% 2.03/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f7])).
% 2.03/0.99  
% 2.03/0.99  fof(f8,axiom,(
% 2.03/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f58,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f8])).
% 2.03/0.99  
% 2.03/0.99  fof(f9,axiom,(
% 2.03/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f59,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f9])).
% 2.03/0.99  
% 2.03/0.99  fof(f82,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.03/0.99    inference(definition_unfolding,[],[f58,f59])).
% 2.03/0.99  
% 2.03/0.99  fof(f85,plain,(
% 2.03/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.03/0.99    inference(definition_unfolding,[],[f57,f82])).
% 2.03/0.99  
% 2.03/0.99  fof(f15,axiom,(
% 2.03/0.99    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f67,plain,(
% 2.03/0.99    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f15])).
% 2.03/0.99  
% 2.03/0.99  fof(f19,axiom,(
% 2.03/0.99    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f71,plain,(
% 2.03/0.99    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 2.03/0.99    inference(cnf_transformation,[],[f19])).
% 2.03/0.99  
% 2.03/0.99  fof(f18,axiom,(
% 2.03/0.99    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f70,plain,(
% 2.03/0.99    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.03/0.99    inference(cnf_transformation,[],[f18])).
% 2.03/0.99  
% 2.03/0.99  fof(f86,plain,(
% 2.03/0.99    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 2.03/0.99    inference(definition_unfolding,[],[f71,f70])).
% 2.03/0.99  
% 2.03/0.99  fof(f87,plain,(
% 2.03/0.99    ( ! [X0] : (k1_zfmisc_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 2.03/0.99    inference(definition_unfolding,[],[f67,f86])).
% 2.03/0.99  
% 2.03/0.99  fof(f92,plain,(
% 2.03/0.99    k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0)))),
% 2.03/0.99    inference(definition_unfolding,[],[f61,f85,f87])).
% 2.03/0.99  
% 2.03/0.99  fof(f10,axiom,(
% 2.03/0.99    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f26,plain,(
% 2.03/0.99    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.03/0.99    inference(ennf_transformation,[],[f10])).
% 2.03/0.99  
% 2.03/0.99  fof(f60,plain,(
% 2.03/0.99    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f26])).
% 2.03/0.99  
% 2.03/0.99  fof(f91,plain,(
% 2.03/0.99    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.03/0.99    inference(definition_unfolding,[],[f60,f85])).
% 2.03/0.99  
% 2.03/0.99  fof(f6,axiom,(
% 2.03/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f56,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f6])).
% 2.03/0.99  
% 2.03/0.99  fof(f90,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.03/0.99    inference(definition_unfolding,[],[f56,f82,f82])).
% 2.03/0.99  
% 2.03/0.99  fof(f1,axiom,(
% 2.03/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f38,plain,(
% 2.03/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.03/0.99    inference(nnf_transformation,[],[f1])).
% 2.03/0.99  
% 2.03/0.99  fof(f39,plain,(
% 2.03/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.03/0.99    inference(rectify,[],[f38])).
% 2.03/0.99  
% 2.03/0.99  fof(f40,plain,(
% 2.03/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f41,plain,(
% 2.03/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 2.03/0.99  
% 2.03/0.99  fof(f50,plain,(
% 2.03/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f41])).
% 2.03/0.99  
% 2.03/0.99  fof(f3,axiom,(
% 2.03/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f24,plain,(
% 2.03/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.03/0.99    inference(rectify,[],[f3])).
% 2.03/0.99  
% 2.03/0.99  fof(f25,plain,(
% 2.03/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.03/0.99    inference(ennf_transformation,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f42,plain,(
% 2.03/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f43,plain,(
% 2.03/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f42])).
% 2.03/0.99  
% 2.03/0.99  fof(f53,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.03/0.99    inference(cnf_transformation,[],[f43])).
% 2.03/0.99  
% 2.03/0.99  fof(f13,axiom,(
% 2.03/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f63,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.03/0.99    inference(cnf_transformation,[],[f13])).
% 2.03/0.99  
% 2.03/0.99  fof(f83,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.03/0.99    inference(definition_unfolding,[],[f63,f82])).
% 2.03/0.99  
% 2.03/0.99  fof(f88,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.03/0.99    inference(definition_unfolding,[],[f53,f83])).
% 2.03/0.99  
% 2.03/0.99  fof(f14,axiom,(
% 2.03/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f28,plain,(
% 2.03/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.03/0.99    inference(ennf_transformation,[],[f14])).
% 2.03/0.99  
% 2.03/0.99  fof(f44,plain,(
% 2.03/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f45,plain,(
% 2.03/0.99    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 2.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f44])).
% 2.03/0.99  
% 2.03/0.99  fof(f64,plain,(
% 2.03/0.99    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.03/0.99    inference(cnf_transformation,[],[f45])).
% 2.03/0.99  
% 2.03/0.99  fof(f49,plain,(
% 2.03/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f41])).
% 2.03/0.99  
% 2.03/0.99  fof(f22,conjecture,(
% 2.03/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f23,negated_conjecture,(
% 2.03/0.99    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.03/0.99    inference(negated_conjecture,[],[f22])).
% 2.03/0.99  
% 2.03/0.99  fof(f36,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f23])).
% 2.03/0.99  
% 2.03/0.99  fof(f37,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f36])).
% 2.03/0.99  
% 2.03/0.99  fof(f47,plain,(
% 2.03/0.99    ( ! [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK4))) )),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f46,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f48,plain,(
% 2.03/0.99    (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 2.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f47,f46])).
% 2.03/0.99  
% 2.03/0.99  fof(f80,plain,(
% 2.03/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))),
% 2.03/0.99    inference(cnf_transformation,[],[f48])).
% 2.03/0.99  
% 2.03/0.99  fof(f96,plain,(
% 2.03/0.99    m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))),
% 2.03/0.99    inference(definition_unfolding,[],[f80,f87,f70])).
% 2.03/0.99  
% 2.03/0.99  fof(f78,plain,(
% 2.03/0.99    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 2.03/0.99    inference(cnf_transformation,[],[f48])).
% 2.03/0.99  
% 2.03/0.99  fof(f98,plain,(
% 2.03/0.99    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 2.03/0.99    inference(definition_unfolding,[],[f78,f70])).
% 2.03/0.99  
% 2.03/0.99  fof(f79,plain,(
% 2.03/0.99    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 2.03/0.99    inference(cnf_transformation,[],[f48])).
% 2.03/0.99  
% 2.03/0.99  fof(f97,plain,(
% 2.03/0.99    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 2.03/0.99    inference(definition_unfolding,[],[f79,f70])).
% 2.03/0.99  
% 2.03/0.99  fof(f21,axiom,(
% 2.03/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f34,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f21])).
% 2.03/0.99  
% 2.03/0.99  fof(f35,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.03/0.99    inference(flattening,[],[f34])).
% 2.03/0.99  
% 2.03/0.99  fof(f73,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f35])).
% 2.03/0.99  
% 2.03/0.99  fof(f95,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.03/0.99    inference(definition_unfolding,[],[f73,f87,f70,f70,f70,f70])).
% 2.03/0.99  
% 2.03/0.99  fof(f77,plain,(
% 2.03/0.99    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))),
% 2.03/0.99    inference(cnf_transformation,[],[f48])).
% 2.03/0.99  
% 2.03/0.99  fof(f99,plain,(
% 2.03/0.99    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))),
% 2.03/0.99    inference(definition_unfolding,[],[f77,f70])).
% 2.03/0.99  
% 2.03/0.99  fof(f76,plain,(
% 2.03/0.99    ~v1_xboole_0(sK4)),
% 2.03/0.99    inference(cnf_transformation,[],[f48])).
% 2.03/0.99  
% 2.03/0.99  fof(f75,plain,(
% 2.03/0.99    l1_struct_0(sK3)),
% 2.03/0.99    inference(cnf_transformation,[],[f48])).
% 2.03/0.99  
% 2.03/0.99  fof(f2,axiom,(
% 2.03/0.99    v1_xboole_0(k1_xboole_0)),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f51,plain,(
% 2.03/0.99    v1_xboole_0(k1_xboole_0)),
% 2.03/0.99    inference(cnf_transformation,[],[f2])).
% 2.03/0.99  
% 2.03/0.99  fof(f17,axiom,(
% 2.03/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f30,plain,(
% 2.03/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f17])).
% 2.03/0.99  
% 2.03/0.99  fof(f31,plain,(
% 2.03/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f30])).
% 2.03/0.99  
% 2.03/0.99  fof(f69,plain,(
% 2.03/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f31])).
% 2.03/0.99  
% 2.03/0.99  fof(f74,plain,(
% 2.03/0.99    ~v2_struct_0(sK3)),
% 2.03/0.99    inference(cnf_transformation,[],[f48])).
% 2.03/0.99  
% 2.03/0.99  fof(f16,axiom,(
% 2.03/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f29,plain,(
% 2.03/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f16])).
% 2.03/0.99  
% 2.03/0.99  fof(f68,plain,(
% 2.03/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f29])).
% 2.03/0.99  
% 2.03/0.99  fof(f20,axiom,(
% 2.03/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f32,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f20])).
% 2.03/0.99  
% 2.03/0.99  fof(f33,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f32])).
% 2.03/0.99  
% 2.03/0.99  fof(f72,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f33])).
% 2.03/0.99  
% 2.03/0.99  fof(f94,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(definition_unfolding,[],[f72,f70,f85,f87,f70,f70,f70])).
% 2.03/0.99  
% 2.03/0.99  fof(f12,axiom,(
% 2.03/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f27,plain,(
% 2.03/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f12])).
% 2.03/0.99  
% 2.03/0.99  fof(f62,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.03/0.99    inference(cnf_transformation,[],[f27])).
% 2.03/0.99  
% 2.03/0.99  fof(f4,axiom,(
% 2.03/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f54,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.03/0.99    inference(cnf_transformation,[],[f4])).
% 2.03/0.99  
% 2.03/0.99  fof(f84,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.03/0.99    inference(definition_unfolding,[],[f54,f83])).
% 2.03/0.99  
% 2.03/0.99  fof(f93,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 2.03/0.99    inference(definition_unfolding,[],[f62,f84,f87])).
% 2.03/0.99  
% 2.03/0.99  fof(f5,axiom,(
% 2.03/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f55,plain,(
% 2.03/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.03/0.99    inference(cnf_transformation,[],[f5])).
% 2.03/0.99  
% 2.03/0.99  fof(f81,plain,(
% 2.03/0.99    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4),
% 2.03/0.99    inference(cnf_transformation,[],[f48])).
% 2.03/0.99  
% 2.03/0.99  cnf(c_8,plain,
% 2.03/0.99      ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0))) ),
% 2.03/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_7,plain,
% 2.03/0.99      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1537,plain,
% 2.03/0.99      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
% 2.03/0.99      | r2_hidden(X0,X1) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2309,plain,
% 2.03/0.99      ( r1_xboole_0(u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0))),X0) = iProver_top
% 2.03/0.99      | r2_hidden(k1_xboole_0,X0) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_8,c_1537]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_6,plain,
% 2.03/0.99      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_0,plain,
% 2.03/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1542,plain,
% 2.03/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.03/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3,plain,
% 2.03/0.99      ( ~ r1_xboole_0(X0,X1)
% 2.03/0.99      | ~ r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 2.03/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1539,plain,
% 2.03/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 2.03/0.99      | r2_hidden(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2582,plain,
% 2.03/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 2.03/0.99      | v1_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1542,c_1539]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2764,plain,
% 2.03/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 2.03/0.99      | v1_xboole_0(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_6,c_2582]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_12,plain,
% 2.03/0.99      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.03/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1534,plain,
% 2.03/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1,plain,
% 2.03/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1541,plain,
% 2.03/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.03/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2181,plain,
% 2.03/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1534,c_1541]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2918,plain,
% 2.03/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0
% 2.03/0.99      | r1_xboole_0(X1,X0) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_2764,c_2181]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3165,plain,
% 2.03/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0))))) = k1_xboole_0
% 2.03/0.99      | r2_hidden(k1_xboole_0,X0) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_2309,c_2918]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_18,negated_conjecture,
% 2.03/0.99      ( m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))))) ),
% 2.03/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_20,negated_conjecture,
% 2.03/0.99      ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.03/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_19,negated_conjecture,
% 2.03/0.99      ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.03/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_16,plain,
% 2.03/0.99      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.03/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))
% 2.03/0.99      | ~ r2_hidden(X2,X0)
% 2.03/0.99      | ~ v1_xboole_0(X2)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_21,negated_conjecture,
% 2.03/0.99      ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
% 2.03/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_272,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))
% 2.03/0.99      | ~ r2_hidden(X2,X0)
% 2.03/0.99      | ~ v1_xboole_0(X2)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | sK4 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_273,plain,
% 2.03/0.99      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 2.03/0.99      | ~ r2_hidden(X1,sK4)
% 2.03/0.99      | ~ v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(sK4)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_272]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_22,negated_conjecture,
% 2.03/0.99      ( ~ v1_xboole_0(sK4) ),
% 2.03/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_275,plain,
% 2.03/0.99      ( v1_xboole_0(X0)
% 2.03/0.99      | ~ v1_xboole_0(X1)
% 2.03/0.99      | ~ r2_hidden(X1,sK4)
% 2.03/0.99      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 2.03/0.99      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_273,c_22]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_276,plain,
% 2.03/0.99      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 2.03/0.99      | ~ r2_hidden(X1,sK4)
% 2.03/0.99      | ~ v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_275]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_357,plain,
% 2.03/0.99      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 2.03/0.99      | ~ r2_hidden(X1,sK4)
% 2.03/0.99      | ~ v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.03/0.99      | sK4 != sK4 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_276]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_402,plain,
% 2.03/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 2.03/0.99      | ~ r2_hidden(X1,sK4)
% 2.03/0.99      | ~ v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.03/0.99      | sK4 != sK4 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_357]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_443,plain,
% 2.03/0.99      ( ~ r2_hidden(X0,sK4)
% 2.03/0.99      | ~ v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.03/0.99      | sK4 != sK4 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_402]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_832,plain,
% 2.03/0.99      ( ~ r2_hidden(X0,sK4)
% 2.03/0.99      | ~ v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1)) ),
% 2.03/0.99      inference(equality_resolution_simp,[status(thm)],[c_443]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1246,plain,
% 2.03/0.99      ( ~ r2_hidden(X0,sK4) | ~ v1_xboole_0(X0) | ~ sP1_iProver_split ),
% 2.03/0.99      inference(splitting,
% 2.03/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.03/0.99                [c_832]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1530,plain,
% 2.03/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.03/0.99      | v1_xboole_0(X0) != iProver_top
% 2.03/0.99      | sP1_iProver_split != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1246]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3389,plain,
% 2.03/0.99      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0))))) = k1_xboole_0
% 2.03/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top
% 2.03/0.99      | sP1_iProver_split != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_3165,c_1530]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_23,negated_conjecture,
% 2.03/0.99      ( l1_struct_0(sK3) ),
% 2.03/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_26,plain,
% 2.03/0.99      ( l1_struct_0(sK3) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2,plain,
% 2.03/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_63,plain,
% 2.03/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_14,plain,
% 2.03/0.99      ( v2_struct_0(X0)
% 2.03/0.99      | ~ l1_struct_0(X0)
% 2.03/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.03/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_24,negated_conjecture,
% 2.03/0.99      ( ~ v2_struct_0(sK3) ),
% 2.03/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_309,plain,
% 2.03/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_310,plain,
% 2.03/0.99      ( ~ l1_struct_0(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_309]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_311,plain,
% 2.03/0.99      ( l1_struct_0(sK3) != iProver_top
% 2.03/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1247,plain,
% 2.03/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 2.03/0.99      inference(splitting,
% 2.03/0.99                [splitting(split),new_symbols(definition,[])],
% 2.03/0.99                [c_832]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1278,plain,
% 2.03/0.99      ( sP1_iProver_split = iProver_top
% 2.03/0.99      | sP0_iProver_split = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1247]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1245,plain,
% 2.03/0.99      ( v1_xboole_0(X0)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.03/0.99      | ~ sP0_iProver_split ),
% 2.03/0.99      inference(splitting,
% 2.03/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.03/0.99                [c_832]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1531,plain,
% 2.03/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.03/0.99      | v1_xboole_0(X0) = iProver_top
% 2.03/0.99      | sP0_iProver_split != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1245]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_13,plain,
% 2.03/0.99      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_351,plain,
% 2.03/0.99      ( k2_struct_0(X0) = u1_struct_0(X0) | sK3 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_352,plain,
% 2.03/0.99      ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_351]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1614,plain,
% 2.03/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.03/0.99      | v1_xboole_0(X0) = iProver_top
% 2.03/0.99      | sP0_iProver_split != iProver_top ),
% 2.03/0.99      inference(light_normalisation,[status(thm)],[c_1531,c_352]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1732,plain,
% 2.03/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))
% 2.03/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK3))) != k3_lattice3(k1_lattice3(u1_struct_0(sK3)))
% 2.03/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 2.03/0.99      | sP0_iProver_split != iProver_top ),
% 2.03/0.99      inference(equality_resolution,[status(thm)],[c_1614]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2033,plain,
% 2.03/0.99      ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 2.03/0.99      | sP0_iProver_split != iProver_top ),
% 2.03/0.99      inference(equality_resolution_simp,[status(thm)],[c_1732]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3424,plain,
% 2.03/0.99      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0))))) = k1_xboole_0 ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_3389,c_26,c_63,c_311,c_1278,c_2033]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_15,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.03/0.99      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))
% 2.03/0.99      | v2_struct_0(X1)
% 2.03/0.99      | ~ l1_struct_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
% 2.03/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_320,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.03/0.99      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))
% 2.03/0.99      | ~ l1_struct_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
% 2.03/0.99      | sK3 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_321,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.03/0.99      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 2.03/0.99      | ~ l1_struct_0(sK3)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_320]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_323,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.03/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_321,c_23]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_324,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.03/0.99      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_323]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_384,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.03/0.99      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 2.03/0.99      | sK4 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_324]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_385,plain,
% 2.03/0.99      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.03/0.99      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 2.03/0.99      | v1_xboole_0(sK4)
% 2.03/0.99      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_384]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_387,plain,
% 2.03/0.99      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_385,c_22,c_20,c_18]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1594,plain,
% 2.03/0.99      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))),sK4,u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0)))) = k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) ),
% 2.03/0.99      inference(light_normalisation,[status(thm)],[c_387,c_8,c_352]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_9,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.03/0.99      | k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 2.03/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_434,plain,
% 2.03/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X2)))
% 2.03/0.99      | sK4 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_435,plain,
% 2.03/0.99      ( k5_xboole_0(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,X0))) = k7_subset_1(X1,sK4,X0)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X1))) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_434]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1609,plain,
% 2.03/0.99      ( k5_xboole_0(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,X0))) = k7_subset_1(X1,sK4,X0)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X1))) ),
% 2.03/0.99      inference(light_normalisation,[status(thm)],[c_435,c_352]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1701,plain,
% 2.03/0.99      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))),sK4,X0) = k5_xboole_0(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,X0))) ),
% 2.03/0.99      inference(equality_resolution,[status(thm)],[c_1609]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1997,plain,
% 2.03/0.99      ( k5_xboole_0(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,u1_struct_0(k3_lattice3(k1_lattice3(k1_xboole_0)))))) = k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1594,c_1701]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3427,plain,
% 2.03/0.99      ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) = k5_xboole_0(sK4,k1_xboole_0) ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_3424,c_1997]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_5,plain,
% 2.03/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.03/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3428,plain,
% 2.03/0.99      ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) = sK4 ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_3427,c_5]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_17,negated_conjecture,
% 2.03/0.99      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
% 2.03/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1557,plain,
% 2.03/0.99      ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) != sK4 ),
% 2.03/0.99      inference(light_normalisation,[status(thm)],[c_17,c_352]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(contradiction,plain,
% 2.03/0.99      ( $false ),
% 2.03/0.99      inference(minisat,[status(thm)],[c_3428,c_1557]) ).
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  ------                               Statistics
% 2.03/0.99  
% 2.03/0.99  ------ General
% 2.03/0.99  
% 2.03/0.99  abstr_ref_over_cycles:                  0
% 2.03/0.99  abstr_ref_under_cycles:                 0
% 2.03/0.99  gc_basic_clause_elim:                   0
% 2.03/0.99  forced_gc_time:                         0
% 2.03/0.99  parsing_time:                           0.009
% 2.03/0.99  unif_index_cands_time:                  0.
% 2.03/0.99  unif_index_add_time:                    0.
% 2.03/0.99  orderings_time:                         0.
% 2.03/0.99  out_proof_time:                         0.009
% 2.03/0.99  total_time:                             0.139
% 2.03/0.99  num_of_symbols:                         59
% 2.03/0.99  num_of_terms:                           2593
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing
% 2.03/0.99  
% 2.03/0.99  num_of_splits:                          2
% 2.03/0.99  num_of_split_atoms:                     2
% 2.03/0.99  num_of_reused_defs:                     0
% 2.03/0.99  num_eq_ax_congr_red:                    29
% 2.03/0.99  num_of_sem_filtered_clauses:            1
% 2.03/0.99  num_of_subtypes:                        0
% 2.03/0.99  monotx_restored_types:                  0
% 2.03/0.99  sat_num_of_epr_types:                   0
% 2.03/0.99  sat_num_of_non_cyclic_types:            0
% 2.03/0.99  sat_guarded_non_collapsed_types:        0
% 2.03/0.99  num_pure_diseq_elim:                    0
% 2.03/0.99  simp_replaced_by:                       0
% 2.03/0.99  res_preprocessed:                       117
% 2.03/0.99  prep_upred:                             0
% 2.03/0.99  prep_unflattend:                        74
% 2.03/0.99  smt_new_axioms:                         0
% 2.03/0.99  pred_elim_cands:                        3
% 2.03/0.99  pred_elim:                              6
% 2.03/0.99  pred_elim_cl:                           6
% 2.03/0.99  pred_elim_cycles:                       10
% 2.03/0.99  merged_defs:                            0
% 2.03/0.99  merged_defs_ncl:                        0
% 2.03/0.99  bin_hyper_res:                          0
% 2.03/0.99  prep_cycles:                            4
% 2.03/0.99  pred_elim_time:                         0.02
% 2.03/0.99  splitting_time:                         0.
% 2.03/0.99  sem_filter_time:                        0.
% 2.03/0.99  monotx_time:                            0.001
% 2.03/0.99  subtype_inf_time:                       0.
% 2.03/0.99  
% 2.03/0.99  ------ Problem properties
% 2.03/0.99  
% 2.03/0.99  clauses:                                21
% 2.03/0.99  conjectures:                            2
% 2.03/0.99  epr:                                    5
% 2.03/0.99  horn:                                   16
% 2.03/0.99  ground:                                 8
% 2.03/0.99  unary:                                  9
% 2.03/0.99  binary:                                 8
% 2.03/0.99  lits:                                   39
% 2.03/0.99  lits_eq:                                16
% 2.03/0.99  fd_pure:                                0
% 2.03/0.99  fd_pseudo:                              0
% 2.03/0.99  fd_cond:                                3
% 2.03/0.99  fd_pseudo_cond:                         0
% 2.03/0.99  ac_symbols:                             0
% 2.03/0.99  
% 2.03/0.99  ------ Propositional Solver
% 2.03/0.99  
% 2.03/0.99  prop_solver_calls:                      28
% 2.03/0.99  prop_fast_solver_calls:                 808
% 2.03/0.99  smt_solver_calls:                       0
% 2.03/0.99  smt_fast_solver_calls:                  0
% 2.03/0.99  prop_num_of_clauses:                    987
% 2.03/0.99  prop_preprocess_simplified:             4031
% 2.03/0.99  prop_fo_subsumed:                       20
% 2.03/0.99  prop_solver_time:                       0.
% 2.03/0.99  smt_solver_time:                        0.
% 2.03/0.99  smt_fast_solver_time:                   0.
% 2.03/0.99  prop_fast_solver_time:                  0.
% 2.03/0.99  prop_unsat_core_time:                   0.
% 2.03/0.99  
% 2.03/0.99  ------ QBF
% 2.03/0.99  
% 2.03/0.99  qbf_q_res:                              0
% 2.03/0.99  qbf_num_tautologies:                    0
% 2.03/0.99  qbf_prep_cycles:                        0
% 2.03/0.99  
% 2.03/0.99  ------ BMC1
% 2.03/0.99  
% 2.03/0.99  bmc1_current_bound:                     -1
% 2.03/0.99  bmc1_last_solved_bound:                 -1
% 2.03/0.99  bmc1_unsat_core_size:                   -1
% 2.03/0.99  bmc1_unsat_core_parents_size:           -1
% 2.03/0.99  bmc1_merge_next_fun:                    0
% 2.03/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation
% 2.03/0.99  
% 2.03/0.99  inst_num_of_clauses:                    352
% 2.03/0.99  inst_num_in_passive:                    126
% 2.03/0.99  inst_num_in_active:                     190
% 2.03/0.99  inst_num_in_unprocessed:                36
% 2.03/0.99  inst_num_of_loops:                      230
% 2.03/0.99  inst_num_of_learning_restarts:          0
% 2.03/0.99  inst_num_moves_active_passive:          37
% 2.03/0.99  inst_lit_activity:                      0
% 2.03/0.99  inst_lit_activity_moves:                0
% 2.03/0.99  inst_num_tautologies:                   0
% 2.03/0.99  inst_num_prop_implied:                  0
% 2.03/0.99  inst_num_existing_simplified:           0
% 2.03/0.99  inst_num_eq_res_simplified:             0
% 2.03/0.99  inst_num_child_elim:                    0
% 2.03/0.99  inst_num_of_dismatching_blockings:      31
% 2.03/0.99  inst_num_of_non_proper_insts:           256
% 2.03/0.99  inst_num_of_duplicates:                 0
% 2.03/0.99  inst_inst_num_from_inst_to_res:         0
% 2.03/0.99  inst_dismatching_checking_time:         0.
% 2.03/0.99  
% 2.03/0.99  ------ Resolution
% 2.03/0.99  
% 2.03/0.99  res_num_of_clauses:                     0
% 2.03/0.99  res_num_in_passive:                     0
% 2.03/0.99  res_num_in_active:                      0
% 2.03/0.99  res_num_of_loops:                       121
% 2.03/0.99  res_forward_subset_subsumed:            42
% 2.03/0.99  res_backward_subset_subsumed:           4
% 2.03/0.99  res_forward_subsumed:                   0
% 2.03/0.99  res_backward_subsumed:                  0
% 2.03/0.99  res_forward_subsumption_resolution:     0
% 2.03/0.99  res_backward_subsumption_resolution:    4
% 2.03/0.99  res_clause_to_clause_subsumption:       226
% 2.03/0.99  res_orphan_elimination:                 0
% 2.03/0.99  res_tautology_del:                      29
% 2.03/0.99  res_num_eq_res_simplified:              1
% 2.03/0.99  res_num_sel_changes:                    0
% 2.03/0.99  res_moves_from_active_to_pass:          0
% 2.03/0.99  
% 2.03/0.99  ------ Superposition
% 2.03/0.99  
% 2.03/0.99  sup_time_total:                         0.
% 2.03/0.99  sup_time_generating:                    0.
% 2.03/0.99  sup_time_sim_full:                      0.
% 2.03/0.99  sup_time_sim_immed:                     0.
% 2.03/0.99  
% 2.03/0.99  sup_num_of_clauses:                     54
% 2.03/0.99  sup_num_in_active:                      44
% 2.03/0.99  sup_num_in_passive:                     10
% 2.03/0.99  sup_num_of_loops:                       45
% 2.03/0.99  sup_fw_superposition:                   45
% 2.03/0.99  sup_bw_superposition:                   27
% 2.03/0.99  sup_immediate_simplified:               1
% 2.03/0.99  sup_given_eliminated:                   0
% 2.03/0.99  comparisons_done:                       0
% 2.03/0.99  comparisons_avoided:                    0
% 2.03/0.99  
% 2.03/0.99  ------ Simplifications
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  sim_fw_subset_subsumed:                 0
% 2.03/0.99  sim_bw_subset_subsumed:                 0
% 2.03/0.99  sim_fw_subsumed:                        0
% 2.03/0.99  sim_bw_subsumed:                        0
% 2.03/0.99  sim_fw_subsumption_res:                 0
% 2.03/0.99  sim_bw_subsumption_res:                 0
% 2.03/0.99  sim_tautology_del:                      7
% 2.03/0.99  sim_eq_tautology_del:                   1
% 2.03/0.99  sim_eq_res_simp:                        1
% 2.03/0.99  sim_fw_demodulated:                     1
% 2.03/0.99  sim_bw_demodulated:                     1
% 2.03/0.99  sim_light_normalised:                   4
% 2.03/0.99  sim_joinable_taut:                      0
% 2.03/0.99  sim_joinable_simp:                      0
% 2.03/0.99  sim_ac_normalised:                      0
% 2.03/0.99  sim_smt_subsumption:                    0
% 2.03/0.99  
%------------------------------------------------------------------------------
