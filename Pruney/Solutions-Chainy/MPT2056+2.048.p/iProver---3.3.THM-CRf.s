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
% DateTime   : Thu Dec  3 12:29:13 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 778 expanded)
%              Number of clauses        :   84 ( 194 expanded)
%              Number of leaves         :   20 ( 221 expanded)
%              Depth                    :   28
%              Number of atoms          :  474 (4196 expanded)
%              Number of equality atoms :  148 ( 783 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f32])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f30])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) != sK3
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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
          ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
    & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
    & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    & ~ v1_xboole_0(sK3)
    & l1_struct_0(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f35,f34])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
    inference(definition_unfolding,[],[f59,f50])).

fof(f57,plain,(
    v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(definition_unfolding,[],[f57,f50])).

fof(f58,plain,(
    v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(definition_unfolding,[],[f58,f50])).

fof(f13,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f52,f50,f50,f50,f50])).

fof(f56,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(definition_unfolding,[],[f56,f50])).

fof(f55,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f12,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f51,f50,f50,f50,f50])).

fof(f60,plain,(
    k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f42,f41])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1254,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1249,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k1_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1246,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1252,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1822,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_1252])).

cnf(c_2007,plain,
    ( k3_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1822])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_17,negated_conjecture,
    ( v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_16,negated_conjecture,
    ( v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_18,negated_conjecture,
    ( v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_230,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_231,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK3)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_233,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_231,c_19])).

cnf(c_234,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK3)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_233])).

cnf(c_313,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK3)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_234])).

cnf(c_358,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK3)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_313])).

cnf(c_399,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_358])).

cnf(c_667,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
    inference(equality_resolution_simp,[status(thm)],[c_399])).

cnf(c_955,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ v1_xboole_0(X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_667])).

cnf(c_1242,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_955])).

cnf(c_2249,plain,
    ( k3_xboole_0(k1_tarski(X0),sK3) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2007,c_1242])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_33,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_35,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_956,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_667])).

cnf(c_990,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_958,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1359,plain,
    ( k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) = k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_971,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1406,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) = u1_struct_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != X0 ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_1498,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) = u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_1499,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) = k3_lattice3(k1_lattice3(k2_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_954,plain,
    ( v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_667])).

cnf(c_1568,plain,
    ( v1_xboole_0(k2_struct_0(sK2))
    | ~ sP0_iProver_split
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_1569,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_2269,plain,
    ( v1_xboole_0(X0) != iProver_top
    | k3_xboole_0(k1_tarski(X0),sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2249,c_22,c_23,c_35,c_990,c_1359,c_1498,c_1499,c_1569])).

cnf(c_2270,plain,
    ( k3_xboole_0(k1_tarski(X0),sK3) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2269])).

cnf(c_2277,plain,
    ( k3_xboole_0(k1_tarski(k1_xboole_0),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1254,c_2270])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1251,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2374,plain,
    ( r2_hidden(sK0(k1_tarski(k1_xboole_0),sK3),k1_xboole_0) = iProver_top
    | r1_xboole_0(k1_tarski(k1_xboole_0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2277,c_1251])).

cnf(c_60,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1356,plain,
    ( ~ r2_hidden(k1_xboole_0,sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_1357,plain,
    ( r2_hidden(k1_xboole_0,sK3) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1356])).

cnf(c_1419,plain,
    ( r2_hidden(k1_xboole_0,sK3)
    | r1_xboole_0(k1_tarski(k1_xboole_0),sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1420,plain,
    ( r2_hidden(k1_xboole_0,sK3) = iProver_top
    | r1_xboole_0(k1_tarski(k1_xboole_0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1419])).

cnf(c_2381,plain,
    ( r1_xboole_0(k1_tarski(k1_xboole_0),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2374,c_22,c_23,c_35,c_60,c_990,c_1357,c_1359,c_1420,c_1498,c_1499,c_1569])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1253,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2387,plain,
    ( r1_xboole_0(sK3,k1_tarski(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2381,c_1253])).

cnf(c_2462,plain,
    ( k3_xboole_0(sK3,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2387,c_1822])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_390,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(X2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_391,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = k7_subset_1(X1,sK3,X0)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_1379,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),sK3,X0) = k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) ),
    inference(equality_resolution,[status(thm)],[c_391])).

cnf(c_12,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_267,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_268,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X0)) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_21])).

cnf(c_273,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X0)) ),
    inference(renaming,[status(thm)],[c_272])).

cnf(c_340,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X0))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_273])).

cnf(c_341,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
    | v1_xboole_0(sK3)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),sK3,k1_tarski(k1_xboole_0)) = k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_343,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),sK3,k1_tarski(k1_xboole_0)) = k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_19,c_17,c_15])).

cnf(c_1394,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = k5_xboole_0(sK3,k3_xboole_0(sK3,k1_tarski(k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_1379,c_343])).

cnf(c_14,negated_conjecture,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1417,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k1_tarski(k1_xboole_0))) != sK3 ),
    inference(demodulation,[status(thm)],[c_1394,c_14])).

cnf(c_2810,plain,
    ( k5_xboole_0(sK3,k1_xboole_0) != sK3 ),
    inference(demodulation,[status(thm)],[c_2462,c_1417])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1250,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1829,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1250,c_1822])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1899,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1829,c_4])).

cnf(c_2816,plain,
    ( sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_2810,c_1899])).

cnf(c_2817,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2816])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:01:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.90/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.00  
% 1.90/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.90/1.00  
% 1.90/1.00  ------  iProver source info
% 1.90/1.00  
% 1.90/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.90/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.90/1.00  git: non_committed_changes: false
% 1.90/1.00  git: last_make_outside_of_git: false
% 1.90/1.00  
% 1.90/1.00  ------ 
% 1.90/1.00  
% 1.90/1.00  ------ Input Options
% 1.90/1.00  
% 1.90/1.00  --out_options                           all
% 1.90/1.00  --tptp_safe_out                         true
% 1.90/1.00  --problem_path                          ""
% 1.90/1.00  --include_path                          ""
% 1.90/1.00  --clausifier                            res/vclausify_rel
% 1.90/1.00  --clausifier_options                    --mode clausify
% 1.90/1.00  --stdin                                 false
% 1.90/1.00  --stats_out                             all
% 1.90/1.00  
% 1.90/1.00  ------ General Options
% 1.90/1.00  
% 1.90/1.00  --fof                                   false
% 1.90/1.00  --time_out_real                         305.
% 1.90/1.00  --time_out_virtual                      -1.
% 1.90/1.00  --symbol_type_check                     false
% 1.90/1.00  --clausify_out                          false
% 1.90/1.00  --sig_cnt_out                           false
% 1.90/1.00  --trig_cnt_out                          false
% 1.90/1.00  --trig_cnt_out_tolerance                1.
% 1.90/1.00  --trig_cnt_out_sk_spl                   false
% 1.90/1.00  --abstr_cl_out                          false
% 1.90/1.00  
% 1.90/1.00  ------ Global Options
% 1.90/1.00  
% 1.90/1.00  --schedule                              default
% 1.90/1.00  --add_important_lit                     false
% 1.90/1.00  --prop_solver_per_cl                    1000
% 1.90/1.00  --min_unsat_core                        false
% 1.90/1.00  --soft_assumptions                      false
% 1.90/1.00  --soft_lemma_size                       3
% 1.90/1.00  --prop_impl_unit_size                   0
% 1.90/1.00  --prop_impl_unit                        []
% 1.90/1.00  --share_sel_clauses                     true
% 1.90/1.00  --reset_solvers                         false
% 1.90/1.00  --bc_imp_inh                            [conj_cone]
% 1.90/1.00  --conj_cone_tolerance                   3.
% 1.90/1.00  --extra_neg_conj                        none
% 1.90/1.00  --large_theory_mode                     true
% 1.90/1.00  --prolific_symb_bound                   200
% 1.90/1.00  --lt_threshold                          2000
% 1.90/1.00  --clause_weak_htbl                      true
% 1.90/1.00  --gc_record_bc_elim                     false
% 1.90/1.00  
% 1.90/1.00  ------ Preprocessing Options
% 1.90/1.00  
% 1.90/1.00  --preprocessing_flag                    true
% 1.90/1.00  --time_out_prep_mult                    0.1
% 1.90/1.00  --splitting_mode                        input
% 1.90/1.00  --splitting_grd                         true
% 1.90/1.00  --splitting_cvd                         false
% 1.90/1.00  --splitting_cvd_svl                     false
% 1.90/1.00  --splitting_nvd                         32
% 1.90/1.00  --sub_typing                            true
% 1.90/1.00  --prep_gs_sim                           true
% 1.90/1.00  --prep_unflatten                        true
% 1.90/1.00  --prep_res_sim                          true
% 1.90/1.00  --prep_upred                            true
% 1.90/1.00  --prep_sem_filter                       exhaustive
% 1.90/1.00  --prep_sem_filter_out                   false
% 1.90/1.00  --pred_elim                             true
% 1.90/1.00  --res_sim_input                         true
% 1.90/1.00  --eq_ax_congr_red                       true
% 1.90/1.00  --pure_diseq_elim                       true
% 1.90/1.00  --brand_transform                       false
% 1.90/1.00  --non_eq_to_eq                          false
% 1.90/1.00  --prep_def_merge                        true
% 1.90/1.00  --prep_def_merge_prop_impl              false
% 1.90/1.00  --prep_def_merge_mbd                    true
% 1.90/1.00  --prep_def_merge_tr_red                 false
% 1.90/1.00  --prep_def_merge_tr_cl                  false
% 1.90/1.00  --smt_preprocessing                     true
% 1.90/1.00  --smt_ac_axioms                         fast
% 1.90/1.00  --preprocessed_out                      false
% 1.90/1.00  --preprocessed_stats                    false
% 1.90/1.00  
% 1.90/1.00  ------ Abstraction refinement Options
% 1.90/1.00  
% 1.90/1.00  --abstr_ref                             []
% 1.90/1.00  --abstr_ref_prep                        false
% 1.90/1.00  --abstr_ref_until_sat                   false
% 1.90/1.00  --abstr_ref_sig_restrict                funpre
% 1.90/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.90/1.00  --abstr_ref_under                       []
% 1.90/1.00  
% 1.90/1.00  ------ SAT Options
% 1.90/1.00  
% 1.90/1.00  --sat_mode                              false
% 1.90/1.00  --sat_fm_restart_options                ""
% 1.90/1.00  --sat_gr_def                            false
% 1.90/1.00  --sat_epr_types                         true
% 1.90/1.00  --sat_non_cyclic_types                  false
% 1.90/1.00  --sat_finite_models                     false
% 1.90/1.00  --sat_fm_lemmas                         false
% 1.90/1.00  --sat_fm_prep                           false
% 1.90/1.00  --sat_fm_uc_incr                        true
% 1.90/1.00  --sat_out_model                         small
% 1.90/1.00  --sat_out_clauses                       false
% 1.90/1.00  
% 1.90/1.00  ------ QBF Options
% 1.90/1.00  
% 1.90/1.00  --qbf_mode                              false
% 1.90/1.00  --qbf_elim_univ                         false
% 1.90/1.00  --qbf_dom_inst                          none
% 1.90/1.00  --qbf_dom_pre_inst                      false
% 1.90/1.00  --qbf_sk_in                             false
% 1.90/1.00  --qbf_pred_elim                         true
% 1.90/1.00  --qbf_split                             512
% 1.90/1.00  
% 1.90/1.00  ------ BMC1 Options
% 1.90/1.00  
% 1.90/1.00  --bmc1_incremental                      false
% 1.90/1.00  --bmc1_axioms                           reachable_all
% 1.90/1.00  --bmc1_min_bound                        0
% 1.90/1.00  --bmc1_max_bound                        -1
% 1.90/1.00  --bmc1_max_bound_default                -1
% 1.90/1.00  --bmc1_symbol_reachability              true
% 1.90/1.00  --bmc1_property_lemmas                  false
% 1.90/1.00  --bmc1_k_induction                      false
% 1.90/1.00  --bmc1_non_equiv_states                 false
% 1.90/1.00  --bmc1_deadlock                         false
% 1.90/1.00  --bmc1_ucm                              false
% 1.90/1.00  --bmc1_add_unsat_core                   none
% 1.90/1.00  --bmc1_unsat_core_children              false
% 1.90/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.90/1.00  --bmc1_out_stat                         full
% 1.90/1.00  --bmc1_ground_init                      false
% 1.90/1.00  --bmc1_pre_inst_next_state              false
% 1.90/1.00  --bmc1_pre_inst_state                   false
% 1.90/1.00  --bmc1_pre_inst_reach_state             false
% 1.90/1.00  --bmc1_out_unsat_core                   false
% 1.90/1.00  --bmc1_aig_witness_out                  false
% 1.90/1.00  --bmc1_verbose                          false
% 1.90/1.00  --bmc1_dump_clauses_tptp                false
% 1.90/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.90/1.00  --bmc1_dump_file                        -
% 1.90/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.90/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.90/1.00  --bmc1_ucm_extend_mode                  1
% 1.90/1.00  --bmc1_ucm_init_mode                    2
% 1.90/1.00  --bmc1_ucm_cone_mode                    none
% 1.90/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.90/1.00  --bmc1_ucm_relax_model                  4
% 1.90/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.90/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.90/1.00  --bmc1_ucm_layered_model                none
% 1.90/1.00  --bmc1_ucm_max_lemma_size               10
% 1.90/1.00  
% 1.90/1.00  ------ AIG Options
% 1.90/1.00  
% 1.90/1.00  --aig_mode                              false
% 1.90/1.00  
% 1.90/1.00  ------ Instantiation Options
% 1.90/1.00  
% 1.90/1.00  --instantiation_flag                    true
% 1.90/1.00  --inst_sos_flag                         false
% 1.90/1.00  --inst_sos_phase                        true
% 1.90/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.90/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.90/1.00  --inst_lit_sel_side                     num_symb
% 1.90/1.00  --inst_solver_per_active                1400
% 1.90/1.00  --inst_solver_calls_frac                1.
% 1.90/1.00  --inst_passive_queue_type               priority_queues
% 1.90/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.90/1.00  --inst_passive_queues_freq              [25;2]
% 1.90/1.00  --inst_dismatching                      true
% 1.90/1.00  --inst_eager_unprocessed_to_passive     true
% 1.90/1.00  --inst_prop_sim_given                   true
% 1.90/1.00  --inst_prop_sim_new                     false
% 1.90/1.00  --inst_subs_new                         false
% 1.90/1.00  --inst_eq_res_simp                      false
% 1.90/1.00  --inst_subs_given                       false
% 1.90/1.00  --inst_orphan_elimination               true
% 1.90/1.00  --inst_learning_loop_flag               true
% 1.90/1.00  --inst_learning_start                   3000
% 1.90/1.00  --inst_learning_factor                  2
% 1.90/1.00  --inst_start_prop_sim_after_learn       3
% 1.90/1.00  --inst_sel_renew                        solver
% 1.90/1.00  --inst_lit_activity_flag                true
% 1.90/1.00  --inst_restr_to_given                   false
% 1.90/1.00  --inst_activity_threshold               500
% 1.90/1.00  --inst_out_proof                        true
% 1.90/1.00  
% 1.90/1.00  ------ Resolution Options
% 1.90/1.00  
% 1.90/1.00  --resolution_flag                       true
% 1.90/1.00  --res_lit_sel                           adaptive
% 1.90/1.00  --res_lit_sel_side                      none
% 1.90/1.00  --res_ordering                          kbo
% 1.90/1.00  --res_to_prop_solver                    active
% 1.90/1.00  --res_prop_simpl_new                    false
% 1.90/1.00  --res_prop_simpl_given                  true
% 1.90/1.00  --res_passive_queue_type                priority_queues
% 1.90/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.90/1.00  --res_passive_queues_freq               [15;5]
% 1.90/1.00  --res_forward_subs                      full
% 1.90/1.00  --res_backward_subs                     full
% 1.90/1.00  --res_forward_subs_resolution           true
% 1.90/1.00  --res_backward_subs_resolution          true
% 1.90/1.00  --res_orphan_elimination                true
% 1.90/1.00  --res_time_limit                        2.
% 1.90/1.00  --res_out_proof                         true
% 1.90/1.00  
% 1.90/1.00  ------ Superposition Options
% 1.90/1.00  
% 1.90/1.00  --superposition_flag                    true
% 1.90/1.00  --sup_passive_queue_type                priority_queues
% 1.90/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.90/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.90/1.00  --demod_completeness_check              fast
% 1.90/1.00  --demod_use_ground                      true
% 1.90/1.00  --sup_to_prop_solver                    passive
% 1.90/1.00  --sup_prop_simpl_new                    true
% 1.90/1.00  --sup_prop_simpl_given                  true
% 1.90/1.00  --sup_fun_splitting                     false
% 1.90/1.00  --sup_smt_interval                      50000
% 1.90/1.00  
% 1.90/1.00  ------ Superposition Simplification Setup
% 1.90/1.00  
% 1.90/1.00  --sup_indices_passive                   []
% 1.90/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.90/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.00  --sup_full_bw                           [BwDemod]
% 1.90/1.00  --sup_immed_triv                        [TrivRules]
% 1.90/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.90/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.00  --sup_immed_bw_main                     []
% 1.90/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.90/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/1.00  
% 1.90/1.00  ------ Combination Options
% 1.90/1.00  
% 1.90/1.00  --comb_res_mult                         3
% 1.90/1.00  --comb_sup_mult                         2
% 1.90/1.00  --comb_inst_mult                        10
% 1.90/1.00  
% 1.90/1.00  ------ Debug Options
% 1.90/1.00  
% 1.90/1.00  --dbg_backtrace                         false
% 1.90/1.00  --dbg_dump_prop_clauses                 false
% 1.90/1.00  --dbg_dump_prop_clauses_file            -
% 1.90/1.00  --dbg_out_stat                          false
% 1.90/1.00  ------ Parsing...
% 1.90/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.90/1.00  
% 1.90/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.90/1.00  
% 1.90/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.90/1.00  
% 1.90/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.90/1.00  ------ Proving...
% 1.90/1.00  ------ Problem Properties 
% 1.90/1.00  
% 1.90/1.00  
% 1.90/1.00  clauses                                 18
% 1.90/1.00  conjectures                             2
% 1.90/1.00  EPR                                     6
% 1.90/1.00  Horn                                    14
% 1.90/1.00  unary                                   7
% 1.90/1.00  binary                                  7
% 1.90/1.00  lits                                    35
% 1.90/1.00  lits eq                                 13
% 1.90/1.00  fd_pure                                 0
% 1.90/1.00  fd_pseudo                               0
% 1.90/1.00  fd_cond                                 3
% 1.90/1.00  fd_pseudo_cond                          0
% 1.90/1.00  AC symbols                              0
% 1.90/1.00  
% 1.90/1.00  ------ Schedule dynamic 5 is on 
% 1.90/1.00  
% 1.90/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.90/1.00  
% 1.90/1.00  
% 1.90/1.00  ------ 
% 1.90/1.00  Current options:
% 1.90/1.00  ------ 
% 1.90/1.00  
% 1.90/1.00  ------ Input Options
% 1.90/1.00  
% 1.90/1.00  --out_options                           all
% 1.90/1.00  --tptp_safe_out                         true
% 1.90/1.00  --problem_path                          ""
% 1.90/1.00  --include_path                          ""
% 1.90/1.00  --clausifier                            res/vclausify_rel
% 1.90/1.00  --clausifier_options                    --mode clausify
% 1.90/1.00  --stdin                                 false
% 1.90/1.00  --stats_out                             all
% 1.90/1.00  
% 1.90/1.00  ------ General Options
% 1.90/1.00  
% 1.90/1.00  --fof                                   false
% 1.90/1.00  --time_out_real                         305.
% 1.90/1.00  --time_out_virtual                      -1.
% 1.90/1.00  --symbol_type_check                     false
% 1.90/1.00  --clausify_out                          false
% 1.90/1.00  --sig_cnt_out                           false
% 1.90/1.00  --trig_cnt_out                          false
% 1.90/1.00  --trig_cnt_out_tolerance                1.
% 1.90/1.00  --trig_cnt_out_sk_spl                   false
% 1.90/1.00  --abstr_cl_out                          false
% 1.90/1.00  
% 1.90/1.00  ------ Global Options
% 1.90/1.00  
% 1.90/1.00  --schedule                              default
% 1.90/1.00  --add_important_lit                     false
% 1.90/1.00  --prop_solver_per_cl                    1000
% 1.90/1.00  --min_unsat_core                        false
% 1.90/1.00  --soft_assumptions                      false
% 1.90/1.00  --soft_lemma_size                       3
% 1.90/1.00  --prop_impl_unit_size                   0
% 1.90/1.00  --prop_impl_unit                        []
% 1.90/1.00  --share_sel_clauses                     true
% 1.90/1.00  --reset_solvers                         false
% 1.90/1.00  --bc_imp_inh                            [conj_cone]
% 1.90/1.00  --conj_cone_tolerance                   3.
% 1.90/1.00  --extra_neg_conj                        none
% 1.90/1.00  --large_theory_mode                     true
% 1.90/1.00  --prolific_symb_bound                   200
% 1.90/1.00  --lt_threshold                          2000
% 1.90/1.00  --clause_weak_htbl                      true
% 1.90/1.00  --gc_record_bc_elim                     false
% 1.90/1.00  
% 1.90/1.00  ------ Preprocessing Options
% 1.90/1.00  
% 1.90/1.00  --preprocessing_flag                    true
% 1.90/1.00  --time_out_prep_mult                    0.1
% 1.90/1.00  --splitting_mode                        input
% 1.90/1.00  --splitting_grd                         true
% 1.90/1.00  --splitting_cvd                         false
% 1.90/1.00  --splitting_cvd_svl                     false
% 1.90/1.00  --splitting_nvd                         32
% 1.90/1.00  --sub_typing                            true
% 1.90/1.00  --prep_gs_sim                           true
% 1.90/1.00  --prep_unflatten                        true
% 1.90/1.00  --prep_res_sim                          true
% 1.90/1.00  --prep_upred                            true
% 1.90/1.00  --prep_sem_filter                       exhaustive
% 1.90/1.00  --prep_sem_filter_out                   false
% 1.90/1.00  --pred_elim                             true
% 1.90/1.00  --res_sim_input                         true
% 1.90/1.00  --eq_ax_congr_red                       true
% 1.90/1.00  --pure_diseq_elim                       true
% 1.90/1.00  --brand_transform                       false
% 1.90/1.00  --non_eq_to_eq                          false
% 1.90/1.00  --prep_def_merge                        true
% 1.90/1.00  --prep_def_merge_prop_impl              false
% 1.90/1.00  --prep_def_merge_mbd                    true
% 1.90/1.00  --prep_def_merge_tr_red                 false
% 1.90/1.00  --prep_def_merge_tr_cl                  false
% 1.90/1.00  --smt_preprocessing                     true
% 1.90/1.00  --smt_ac_axioms                         fast
% 1.90/1.00  --preprocessed_out                      false
% 1.90/1.00  --preprocessed_stats                    false
% 1.90/1.00  
% 1.90/1.00  ------ Abstraction refinement Options
% 1.90/1.00  
% 1.90/1.00  --abstr_ref                             []
% 1.90/1.00  --abstr_ref_prep                        false
% 1.90/1.00  --abstr_ref_until_sat                   false
% 1.90/1.00  --abstr_ref_sig_restrict                funpre
% 1.90/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.90/1.00  --abstr_ref_under                       []
% 1.90/1.00  
% 1.90/1.00  ------ SAT Options
% 1.90/1.00  
% 1.90/1.00  --sat_mode                              false
% 1.90/1.00  --sat_fm_restart_options                ""
% 1.90/1.00  --sat_gr_def                            false
% 1.90/1.00  --sat_epr_types                         true
% 1.90/1.00  --sat_non_cyclic_types                  false
% 1.90/1.00  --sat_finite_models                     false
% 1.90/1.00  --sat_fm_lemmas                         false
% 1.90/1.00  --sat_fm_prep                           false
% 1.90/1.00  --sat_fm_uc_incr                        true
% 1.90/1.00  --sat_out_model                         small
% 1.90/1.00  --sat_out_clauses                       false
% 1.90/1.00  
% 1.90/1.00  ------ QBF Options
% 1.90/1.00  
% 1.90/1.00  --qbf_mode                              false
% 1.90/1.00  --qbf_elim_univ                         false
% 1.90/1.00  --qbf_dom_inst                          none
% 1.90/1.00  --qbf_dom_pre_inst                      false
% 1.90/1.00  --qbf_sk_in                             false
% 1.90/1.00  --qbf_pred_elim                         true
% 1.90/1.00  --qbf_split                             512
% 1.90/1.00  
% 1.90/1.00  ------ BMC1 Options
% 1.90/1.00  
% 1.90/1.00  --bmc1_incremental                      false
% 1.90/1.00  --bmc1_axioms                           reachable_all
% 1.90/1.00  --bmc1_min_bound                        0
% 1.90/1.00  --bmc1_max_bound                        -1
% 1.90/1.00  --bmc1_max_bound_default                -1
% 1.90/1.00  --bmc1_symbol_reachability              true
% 1.90/1.00  --bmc1_property_lemmas                  false
% 1.90/1.00  --bmc1_k_induction                      false
% 1.90/1.00  --bmc1_non_equiv_states                 false
% 1.90/1.00  --bmc1_deadlock                         false
% 1.90/1.00  --bmc1_ucm                              false
% 1.90/1.00  --bmc1_add_unsat_core                   none
% 1.90/1.00  --bmc1_unsat_core_children              false
% 1.90/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.90/1.00  --bmc1_out_stat                         full
% 1.90/1.00  --bmc1_ground_init                      false
% 1.90/1.00  --bmc1_pre_inst_next_state              false
% 1.90/1.00  --bmc1_pre_inst_state                   false
% 1.90/1.00  --bmc1_pre_inst_reach_state             false
% 1.90/1.00  --bmc1_out_unsat_core                   false
% 1.90/1.00  --bmc1_aig_witness_out                  false
% 1.90/1.00  --bmc1_verbose                          false
% 1.90/1.00  --bmc1_dump_clauses_tptp                false
% 1.90/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.90/1.00  --bmc1_dump_file                        -
% 1.90/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.90/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.90/1.00  --bmc1_ucm_extend_mode                  1
% 1.90/1.00  --bmc1_ucm_init_mode                    2
% 1.90/1.00  --bmc1_ucm_cone_mode                    none
% 1.90/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.90/1.00  --bmc1_ucm_relax_model                  4
% 1.90/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.90/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.90/1.00  --bmc1_ucm_layered_model                none
% 1.90/1.00  --bmc1_ucm_max_lemma_size               10
% 1.90/1.00  
% 1.90/1.00  ------ AIG Options
% 1.90/1.00  
% 1.90/1.00  --aig_mode                              false
% 1.90/1.00  
% 1.90/1.00  ------ Instantiation Options
% 1.90/1.00  
% 1.90/1.00  --instantiation_flag                    true
% 1.90/1.00  --inst_sos_flag                         false
% 1.90/1.00  --inst_sos_phase                        true
% 1.90/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.90/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.90/1.00  --inst_lit_sel_side                     none
% 1.90/1.00  --inst_solver_per_active                1400
% 1.90/1.00  --inst_solver_calls_frac                1.
% 1.90/1.00  --inst_passive_queue_type               priority_queues
% 1.90/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.90/1.00  --inst_passive_queues_freq              [25;2]
% 1.90/1.00  --inst_dismatching                      true
% 1.90/1.00  --inst_eager_unprocessed_to_passive     true
% 1.90/1.00  --inst_prop_sim_given                   true
% 1.90/1.00  --inst_prop_sim_new                     false
% 1.90/1.00  --inst_subs_new                         false
% 1.90/1.00  --inst_eq_res_simp                      false
% 1.90/1.00  --inst_subs_given                       false
% 1.90/1.00  --inst_orphan_elimination               true
% 1.90/1.00  --inst_learning_loop_flag               true
% 1.90/1.00  --inst_learning_start                   3000
% 1.90/1.00  --inst_learning_factor                  2
% 1.90/1.00  --inst_start_prop_sim_after_learn       3
% 1.90/1.00  --inst_sel_renew                        solver
% 1.90/1.00  --inst_lit_activity_flag                true
% 1.90/1.00  --inst_restr_to_given                   false
% 1.90/1.00  --inst_activity_threshold               500
% 1.90/1.00  --inst_out_proof                        true
% 1.90/1.00  
% 1.90/1.00  ------ Resolution Options
% 1.90/1.00  
% 1.90/1.00  --resolution_flag                       false
% 1.90/1.00  --res_lit_sel                           adaptive
% 1.90/1.00  --res_lit_sel_side                      none
% 1.90/1.00  --res_ordering                          kbo
% 1.90/1.00  --res_to_prop_solver                    active
% 1.90/1.00  --res_prop_simpl_new                    false
% 1.90/1.00  --res_prop_simpl_given                  true
% 1.90/1.00  --res_passive_queue_type                priority_queues
% 1.90/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.90/1.00  --res_passive_queues_freq               [15;5]
% 1.90/1.00  --res_forward_subs                      full
% 1.90/1.00  --res_backward_subs                     full
% 1.90/1.00  --res_forward_subs_resolution           true
% 1.90/1.00  --res_backward_subs_resolution          true
% 1.90/1.00  --res_orphan_elimination                true
% 1.90/1.00  --res_time_limit                        2.
% 1.90/1.00  --res_out_proof                         true
% 1.90/1.00  
% 1.90/1.00  ------ Superposition Options
% 1.90/1.00  
% 1.90/1.00  --superposition_flag                    true
% 1.90/1.00  --sup_passive_queue_type                priority_queues
% 1.90/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.90/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.90/1.00  --demod_completeness_check              fast
% 1.90/1.00  --demod_use_ground                      true
% 1.90/1.00  --sup_to_prop_solver                    passive
% 1.90/1.00  --sup_prop_simpl_new                    true
% 1.90/1.00  --sup_prop_simpl_given                  true
% 1.90/1.00  --sup_fun_splitting                     false
% 1.90/1.00  --sup_smt_interval                      50000
% 1.90/1.00  
% 1.90/1.00  ------ Superposition Simplification Setup
% 1.90/1.00  
% 1.90/1.00  --sup_indices_passive                   []
% 1.90/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.90/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.00  --sup_full_bw                           [BwDemod]
% 1.90/1.00  --sup_immed_triv                        [TrivRules]
% 1.90/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.90/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.00  --sup_immed_bw_main                     []
% 1.90/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.90/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/1.00  
% 1.90/1.00  ------ Combination Options
% 1.90/1.00  
% 1.90/1.00  --comb_res_mult                         3
% 1.90/1.00  --comb_sup_mult                         2
% 1.90/1.00  --comb_inst_mult                        10
% 1.90/1.00  
% 1.90/1.00  ------ Debug Options
% 1.90/1.00  
% 1.90/1.00  --dbg_backtrace                         false
% 1.90/1.00  --dbg_dump_prop_clauses                 false
% 1.90/1.00  --dbg_dump_prop_clauses_file            -
% 1.90/1.00  --dbg_out_stat                          false
% 1.90/1.00  
% 1.90/1.00  
% 1.90/1.00  
% 1.90/1.00  
% 1.90/1.00  ------ Proving...
% 1.90/1.00  
% 1.90/1.00  
% 1.90/1.00  % SZS status Theorem for theBenchmark.p
% 1.90/1.00  
% 1.90/1.00   Resolution empty clause
% 1.90/1.00  
% 1.90/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.90/1.00  
% 1.90/1.00  fof(f1,axiom,(
% 1.90/1.00    v1_xboole_0(k1_xboole_0)),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f37,plain,(
% 1.90/1.00    v1_xboole_0(k1_xboole_0)),
% 1.90/1.00    inference(cnf_transformation,[],[f1])).
% 1.90/1.00  
% 1.90/1.00  fof(f7,axiom,(
% 1.90/1.00    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f19,plain,(
% 1.90/1.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.90/1.00    inference(ennf_transformation,[],[f7])).
% 1.90/1.00  
% 1.90/1.00  fof(f44,plain,(
% 1.90/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.90/1.00    inference(cnf_transformation,[],[f19])).
% 1.90/1.00  
% 1.90/1.00  fof(f9,axiom,(
% 1.90/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f21,plain,(
% 1.90/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.90/1.00    inference(ennf_transformation,[],[f9])).
% 1.90/1.00  
% 1.90/1.00  fof(f32,plain,(
% 1.90/1.00    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 1.90/1.00    introduced(choice_axiom,[])).
% 1.90/1.00  
% 1.90/1.00  fof(f33,plain,(
% 1.90/1.00    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 1.90/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f32])).
% 1.90/1.00  
% 1.90/1.00  fof(f46,plain,(
% 1.90/1.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.90/1.00    inference(cnf_transformation,[],[f33])).
% 1.90/1.00  
% 1.90/1.00  fof(f3,axiom,(
% 1.90/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f16,plain,(
% 1.90/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.90/1.00    inference(rectify,[],[f3])).
% 1.90/1.00  
% 1.90/1.00  fof(f18,plain,(
% 1.90/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.90/1.00    inference(ennf_transformation,[],[f16])).
% 1.90/1.00  
% 1.90/1.00  fof(f30,plain,(
% 1.90/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 1.90/1.00    introduced(choice_axiom,[])).
% 1.90/1.00  
% 1.90/1.00  fof(f31,plain,(
% 1.90/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.90/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f30])).
% 1.90/1.00  
% 1.90/1.00  fof(f40,plain,(
% 1.90/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.90/1.00    inference(cnf_transformation,[],[f31])).
% 1.90/1.00  
% 1.90/1.00  fof(f14,conjecture,(
% 1.90/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f15,negated_conjecture,(
% 1.90/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.90/1.00    inference(negated_conjecture,[],[f14])).
% 1.90/1.00  
% 1.90/1.00  fof(f28,plain,(
% 1.90/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.90/1.00    inference(ennf_transformation,[],[f15])).
% 1.90/1.00  
% 1.90/1.00  fof(f29,plain,(
% 1.90/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.90/1.00    inference(flattening,[],[f28])).
% 1.90/1.00  
% 1.90/1.00  fof(f35,plain,(
% 1.90/1.00    ( ! [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) != sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK3))) )),
% 1.90/1.00    introduced(choice_axiom,[])).
% 1.90/1.00  
% 1.90/1.00  fof(f34,plain,(
% 1.90/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK2) & ~v2_struct_0(sK2))),
% 1.90/1.00    introduced(choice_axiom,[])).
% 1.90/1.00  
% 1.90/1.00  fof(f36,plain,(
% 1.90/1.00    (k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(sK3)) & l1_struct_0(sK2) & ~v2_struct_0(sK2)),
% 1.90/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f35,f34])).
% 1.90/1.00  
% 1.90/1.00  fof(f59,plain,(
% 1.90/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))),
% 1.90/1.00    inference(cnf_transformation,[],[f36])).
% 1.90/1.00  
% 1.90/1.00  fof(f11,axiom,(
% 1.90/1.00    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f50,plain,(
% 1.90/1.00    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.90/1.00    inference(cnf_transformation,[],[f11])).
% 1.90/1.00  
% 1.90/1.00  fof(f65,plain,(
% 1.90/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))),
% 1.90/1.00    inference(definition_unfolding,[],[f59,f50])).
% 1.90/1.00  
% 1.90/1.00  fof(f57,plain,(
% 1.90/1.00    v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))),
% 1.90/1.00    inference(cnf_transformation,[],[f36])).
% 1.90/1.00  
% 1.90/1.00  fof(f67,plain,(
% 1.90/1.00    v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))),
% 1.90/1.00    inference(definition_unfolding,[],[f57,f50])).
% 1.90/1.00  
% 1.90/1.00  fof(f58,plain,(
% 1.90/1.00    v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))),
% 1.90/1.00    inference(cnf_transformation,[],[f36])).
% 1.90/1.00  
% 1.90/1.00  fof(f66,plain,(
% 1.90/1.00    v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))),
% 1.90/1.00    inference(definition_unfolding,[],[f58,f50])).
% 1.90/1.00  
% 1.90/1.00  fof(f13,axiom,(
% 1.90/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f26,plain,(
% 1.90/1.00    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.90/1.00    inference(ennf_transformation,[],[f13])).
% 1.90/1.00  
% 1.90/1.00  fof(f27,plain,(
% 1.90/1.00    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.90/1.00    inference(flattening,[],[f26])).
% 1.90/1.00  
% 1.90/1.00  fof(f52,plain,(
% 1.90/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.90/1.00    inference(cnf_transformation,[],[f27])).
% 1.90/1.00  
% 1.90/1.00  fof(f64,plain,(
% 1.90/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.90/1.00    inference(definition_unfolding,[],[f52,f50,f50,f50,f50])).
% 1.90/1.00  
% 1.90/1.00  fof(f56,plain,(
% 1.90/1.00    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))),
% 1.90/1.00    inference(cnf_transformation,[],[f36])).
% 1.90/1.00  
% 1.90/1.00  fof(f68,plain,(
% 1.90/1.00    v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))),
% 1.90/1.00    inference(definition_unfolding,[],[f56,f50])).
% 1.90/1.00  
% 1.90/1.00  fof(f55,plain,(
% 1.90/1.00    ~v1_xboole_0(sK3)),
% 1.90/1.00    inference(cnf_transformation,[],[f36])).
% 1.90/1.00  
% 1.90/1.00  fof(f53,plain,(
% 1.90/1.00    ~v2_struct_0(sK2)),
% 1.90/1.00    inference(cnf_transformation,[],[f36])).
% 1.90/1.00  
% 1.90/1.00  fof(f54,plain,(
% 1.90/1.00    l1_struct_0(sK2)),
% 1.90/1.00    inference(cnf_transformation,[],[f36])).
% 1.90/1.00  
% 1.90/1.00  fof(f10,axiom,(
% 1.90/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f22,plain,(
% 1.90/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.90/1.00    inference(ennf_transformation,[],[f10])).
% 1.90/1.00  
% 1.90/1.00  fof(f23,plain,(
% 1.90/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.90/1.00    inference(flattening,[],[f22])).
% 1.90/1.00  
% 1.90/1.00  fof(f49,plain,(
% 1.90/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.90/1.00    inference(cnf_transformation,[],[f23])).
% 1.90/1.00  
% 1.90/1.00  fof(f39,plain,(
% 1.90/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.90/1.00    inference(cnf_transformation,[],[f31])).
% 1.90/1.00  
% 1.90/1.00  fof(f2,axiom,(
% 1.90/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f17,plain,(
% 1.90/1.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.90/1.00    inference(ennf_transformation,[],[f2])).
% 1.90/1.00  
% 1.90/1.00  fof(f38,plain,(
% 1.90/1.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.90/1.00    inference(cnf_transformation,[],[f17])).
% 1.90/1.00  
% 1.90/1.00  fof(f8,axiom,(
% 1.90/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f20,plain,(
% 1.90/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.90/1.00    inference(ennf_transformation,[],[f8])).
% 1.90/1.00  
% 1.90/1.00  fof(f45,plain,(
% 1.90/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.90/1.00    inference(cnf_transformation,[],[f20])).
% 1.90/1.00  
% 1.90/1.00  fof(f4,axiom,(
% 1.90/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f41,plain,(
% 1.90/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.90/1.00    inference(cnf_transformation,[],[f4])).
% 1.90/1.00  
% 1.90/1.00  fof(f62,plain,(
% 1.90/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.90/1.00    inference(definition_unfolding,[],[f45,f41])).
% 1.90/1.00  
% 1.90/1.00  fof(f12,axiom,(
% 1.90/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f24,plain,(
% 1.90/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.90/1.00    inference(ennf_transformation,[],[f12])).
% 1.90/1.00  
% 1.90/1.00  fof(f25,plain,(
% 1.90/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.90/1.00    inference(flattening,[],[f24])).
% 1.90/1.00  
% 1.90/1.00  fof(f51,plain,(
% 1.90/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.90/1.00    inference(cnf_transformation,[],[f25])).
% 1.90/1.00  
% 1.90/1.00  fof(f63,plain,(
% 1.90/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.90/1.00    inference(definition_unfolding,[],[f51,f50,f50,f50,f50])).
% 1.90/1.00  
% 1.90/1.00  fof(f60,plain,(
% 1.90/1.00    k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3),
% 1.90/1.00    inference(cnf_transformation,[],[f36])).
% 1.90/1.00  
% 1.90/1.00  fof(f6,axiom,(
% 1.90/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f43,plain,(
% 1.90/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.90/1.00    inference(cnf_transformation,[],[f6])).
% 1.90/1.00  
% 1.90/1.00  fof(f5,axiom,(
% 1.90/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.90/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/1.00  
% 1.90/1.00  fof(f42,plain,(
% 1.90/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.90/1.00    inference(cnf_transformation,[],[f5])).
% 1.90/1.00  
% 1.90/1.00  fof(f61,plain,(
% 1.90/1.00    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.90/1.00    inference(definition_unfolding,[],[f42,f41])).
% 1.90/1.00  
% 1.90/1.00  cnf(c_0,plain,
% 1.90/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.90/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1254,plain,
% 1.90/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_6,plain,
% 1.90/1.00      ( r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1) ),
% 1.90/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1249,plain,
% 1.90/1.00      ( r2_hidden(X0,X1) = iProver_top
% 1.90/1.00      | r1_xboole_0(k1_tarski(X0),X1) = iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_10,plain,
% 1.90/1.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 1.90/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1246,plain,
% 1.90/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2,plain,
% 1.90/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 1.90/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1252,plain,
% 1.90/1.00      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 1.90/1.00      | r1_xboole_0(X1,X2) != iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1822,plain,
% 1.90/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 1.90/1.00      inference(superposition,[status(thm)],[c_1246,c_1252]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2007,plain,
% 1.90/1.00      ( k3_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
% 1.90/1.00      | r2_hidden(X0,X1) = iProver_top ),
% 1.90/1.00      inference(superposition,[status(thm)],[c_1249,c_1822]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_15,negated_conjecture,
% 1.90/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
% 1.90/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_17,negated_conjecture,
% 1.90/1.00      ( v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 1.90/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_16,negated_conjecture,
% 1.90/1.00      ( v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 1.90/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_13,plain,
% 1.90/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.90/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.90/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.90/1.00      | ~ r2_hidden(X2,X0)
% 1.90/1.00      | ~ v1_xboole_0(X2)
% 1.90/1.00      | v1_xboole_0(X0)
% 1.90/1.00      | v1_xboole_0(X1) ),
% 1.90/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_18,negated_conjecture,
% 1.90/1.00      ( v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
% 1.90/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_230,plain,
% 1.90/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.90/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.90/1.00      | ~ r2_hidden(X2,X0)
% 1.90/1.00      | ~ v1_xboole_0(X2)
% 1.90/1.00      | v1_xboole_0(X0)
% 1.90/1.00      | v1_xboole_0(X1)
% 1.90/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.90/1.00      | sK3 != X0 ),
% 1.90/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_231,plain,
% 1.90/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 1.90/1.00      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 1.90/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.90/1.00      | ~ r2_hidden(X1,sK3)
% 1.90/1.00      | ~ v1_xboole_0(X1)
% 1.90/1.00      | v1_xboole_0(X0)
% 1.90/1.00      | v1_xboole_0(sK3)
% 1.90/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.90/1.00      inference(unflattening,[status(thm)],[c_230]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_19,negated_conjecture,
% 1.90/1.00      ( ~ v1_xboole_0(sK3) ),
% 1.90/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_233,plain,
% 1.90/1.00      ( v1_xboole_0(X0)
% 1.90/1.00      | ~ v1_xboole_0(X1)
% 1.90/1.00      | ~ r2_hidden(X1,sK3)
% 1.90/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.90/1.00      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 1.90/1.00      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 1.90/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.90/1.00      inference(global_propositional_subsumption,[status(thm)],[c_231,c_19]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_234,plain,
% 1.90/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 1.90/1.00      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 1.90/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.90/1.00      | ~ r2_hidden(X1,sK3)
% 1.90/1.00      | ~ v1_xboole_0(X1)
% 1.90/1.00      | v1_xboole_0(X0)
% 1.90/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.90/1.00      inference(renaming,[status(thm)],[c_233]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_313,plain,
% 1.90/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 1.90/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.90/1.00      | ~ r2_hidden(X1,sK3)
% 1.90/1.00      | ~ v1_xboole_0(X1)
% 1.90/1.00      | v1_xboole_0(X0)
% 1.90/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.90/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 1.90/1.00      | sK3 != sK3 ),
% 1.90/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_234]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_358,plain,
% 1.90/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.90/1.00      | ~ r2_hidden(X1,sK3)
% 1.90/1.00      | ~ v1_xboole_0(X1)
% 1.90/1.00      | v1_xboole_0(X0)
% 1.90/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.90/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 1.90/1.00      | sK3 != sK3 ),
% 1.90/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_313]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_399,plain,
% 1.90/1.00      ( ~ r2_hidden(X0,sK3)
% 1.90/1.00      | ~ v1_xboole_0(X0)
% 1.90/1.00      | v1_xboole_0(X1)
% 1.90/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.90/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 1.90/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.90/1.00      | sK3 != sK3 ),
% 1.90/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_358]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_667,plain,
% 1.90/1.00      ( ~ r2_hidden(X0,sK3)
% 1.90/1.00      | ~ v1_xboole_0(X0)
% 1.90/1.00      | v1_xboole_0(X1)
% 1.90/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.90/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 1.90/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
% 1.90/1.00      inference(equality_resolution_simp,[status(thm)],[c_399]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_955,plain,
% 1.90/1.00      ( ~ r2_hidden(X0,sK3) | ~ v1_xboole_0(X0) | ~ sP1_iProver_split ),
% 1.90/1.00      inference(splitting,
% 1.90/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.90/1.00                [c_667]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1242,plain,
% 1.90/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 1.90/1.00      | v1_xboole_0(X0) != iProver_top
% 1.90/1.00      | sP1_iProver_split != iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_955]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2249,plain,
% 1.90/1.00      ( k3_xboole_0(k1_tarski(X0),sK3) = k1_xboole_0
% 1.90/1.00      | v1_xboole_0(X0) != iProver_top
% 1.90/1.00      | sP1_iProver_split != iProver_top ),
% 1.90/1.00      inference(superposition,[status(thm)],[c_2007,c_1242]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_21,negated_conjecture,
% 1.90/1.00      ( ~ v2_struct_0(sK2) ),
% 1.90/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_22,plain,
% 1.90/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_20,negated_conjecture,
% 1.90/1.00      ( l1_struct_0(sK2) ),
% 1.90/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_23,plain,
% 1.90/1.00      ( l1_struct_0(sK2) = iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_11,plain,
% 1.90/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 1.90/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_33,plain,
% 1.90/1.00      ( v2_struct_0(X0) = iProver_top
% 1.90/1.00      | l1_struct_0(X0) != iProver_top
% 1.90/1.00      | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_35,plain,
% 1.90/1.00      ( v2_struct_0(sK2) = iProver_top
% 1.90/1.00      | l1_struct_0(sK2) != iProver_top
% 1.90/1.00      | v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
% 1.90/1.00      inference(instantiation,[status(thm)],[c_33]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_956,plain,
% 1.90/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 1.90/1.00      inference(splitting,
% 1.90/1.00                [splitting(split),new_symbols(definition,[])],
% 1.90/1.00                [c_667]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_990,plain,
% 1.90/1.00      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_958,plain,( X0 = X0 ),theory(equality) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1359,plain,
% 1.90/1.00      ( k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) = k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
% 1.90/1.00      inference(instantiation,[status(thm)],[c_958]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_971,plain,
% 1.90/1.00      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 1.90/1.00      theory(equality) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1406,plain,
% 1.90/1.00      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) = u1_struct_0(X0)
% 1.90/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != X0 ),
% 1.90/1.00      inference(instantiation,[status(thm)],[c_971]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1498,plain,
% 1.90/1.00      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) = u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.90/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2))) ),
% 1.90/1.00      inference(instantiation,[status(thm)],[c_1406]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1499,plain,
% 1.90/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) = k3_lattice3(k1_lattice3(k2_struct_0(sK2))) ),
% 1.90/1.00      inference(instantiation,[status(thm)],[c_958]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_954,plain,
% 1.90/1.00      ( v1_xboole_0(X0)
% 1.90/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.90/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 1.90/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 1.90/1.00      | ~ sP0_iProver_split ),
% 1.90/1.00      inference(splitting,
% 1.90/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.90/1.00                [c_667]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1568,plain,
% 1.90/1.00      ( v1_xboole_0(k2_struct_0(sK2))
% 1.90/1.00      | ~ sP0_iProver_split
% 1.90/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.90/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 1.90/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
% 1.90/1.00      inference(instantiation,[status(thm)],[c_954]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1569,plain,
% 1.90/1.00      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.90/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 1.90/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))
% 1.90/1.00      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
% 1.90/1.00      | sP0_iProver_split != iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2269,plain,
% 1.90/1.00      ( v1_xboole_0(X0) != iProver_top
% 1.90/1.00      | k3_xboole_0(k1_tarski(X0),sK3) = k1_xboole_0 ),
% 1.90/1.00      inference(global_propositional_subsumption,
% 1.90/1.00                [status(thm)],
% 1.90/1.00                [c_2249,c_22,c_23,c_35,c_990,c_1359,c_1498,c_1499,c_1569]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2270,plain,
% 1.90/1.00      ( k3_xboole_0(k1_tarski(X0),sK3) = k1_xboole_0
% 1.90/1.00      | v1_xboole_0(X0) != iProver_top ),
% 1.90/1.00      inference(renaming,[status(thm)],[c_2269]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2277,plain,
% 1.90/1.00      ( k3_xboole_0(k1_tarski(k1_xboole_0),sK3) = k1_xboole_0 ),
% 1.90/1.00      inference(superposition,[status(thm)],[c_1254,c_2270]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_3,plain,
% 1.90/1.00      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 1.90/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1251,plain,
% 1.90/1.00      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) = iProver_top
% 1.90/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2374,plain,
% 1.90/1.00      ( r2_hidden(sK0(k1_tarski(k1_xboole_0),sK3),k1_xboole_0) = iProver_top
% 1.90/1.00      | r1_xboole_0(k1_tarski(k1_xboole_0),sK3) = iProver_top ),
% 1.90/1.00      inference(superposition,[status(thm)],[c_2277,c_1251]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_60,plain,
% 1.90/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1356,plain,
% 1.90/1.00      ( ~ r2_hidden(k1_xboole_0,sK3)
% 1.90/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 1.90/1.00      | ~ sP1_iProver_split ),
% 1.90/1.00      inference(instantiation,[status(thm)],[c_955]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1357,plain,
% 1.90/1.00      ( r2_hidden(k1_xboole_0,sK3) != iProver_top
% 1.90/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top
% 1.90/1.00      | sP1_iProver_split != iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1356]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1419,plain,
% 1.90/1.00      ( r2_hidden(k1_xboole_0,sK3) | r1_xboole_0(k1_tarski(k1_xboole_0),sK3) ),
% 1.90/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1420,plain,
% 1.90/1.00      ( r2_hidden(k1_xboole_0,sK3) = iProver_top
% 1.90/1.00      | r1_xboole_0(k1_tarski(k1_xboole_0),sK3) = iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1419]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2381,plain,
% 1.90/1.00      ( r1_xboole_0(k1_tarski(k1_xboole_0),sK3) = iProver_top ),
% 1.90/1.00      inference(global_propositional_subsumption,
% 1.90/1.00                [status(thm)],
% 1.90/1.00                [c_2374,c_22,c_23,c_35,c_60,c_990,c_1357,c_1359,c_1420,
% 1.90/1.00                 c_1498,c_1499,c_1569]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1,plain,
% 1.90/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 1.90/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1253,plain,
% 1.90/1.00      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2387,plain,
% 1.90/1.00      ( r1_xboole_0(sK3,k1_tarski(k1_xboole_0)) = iProver_top ),
% 1.90/1.00      inference(superposition,[status(thm)],[c_2381,c_1253]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2462,plain,
% 1.90/1.00      ( k3_xboole_0(sK3,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
% 1.90/1.00      inference(superposition,[status(thm)],[c_2387,c_1822]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_7,plain,
% 1.90/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.90/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 1.90/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_390,plain,
% 1.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 1.90/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(X2)
% 1.90/1.00      | sK3 != X0 ),
% 1.90/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_391,plain,
% 1.90/1.00      ( k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) = k7_subset_1(X1,sK3,X0)
% 1.90/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) != k1_zfmisc_1(X1) ),
% 1.90/1.00      inference(unflattening,[status(thm)],[c_390]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1379,plain,
% 1.90/1.00      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),sK3,X0) = k5_xboole_0(sK3,k3_xboole_0(sK3,X0)) ),
% 1.90/1.00      inference(equality_resolution,[status(thm)],[c_391]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_12,plain,
% 1.90/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.90/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.90/1.00      | v2_struct_0(X1)
% 1.90/1.00      | ~ l1_struct_0(X1)
% 1.90/1.00      | v1_xboole_0(X0)
% 1.90/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
% 1.90/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_267,plain,
% 1.90/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.90/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.90/1.00      | v2_struct_0(X1)
% 1.90/1.00      | v1_xboole_0(X0)
% 1.90/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
% 1.90/1.00      | sK2 != X1 ),
% 1.90/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_268,plain,
% 1.90/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.90/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
% 1.90/1.00      | v2_struct_0(sK2)
% 1.90/1.00      | v1_xboole_0(X0)
% 1.90/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X0)) ),
% 1.90/1.00      inference(unflattening,[status(thm)],[c_267]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_272,plain,
% 1.90/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
% 1.90/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.90/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.90/1.00      | v1_xboole_0(X0)
% 1.90/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X0)) ),
% 1.90/1.00      inference(global_propositional_subsumption,[status(thm)],[c_268,c_21]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_273,plain,
% 1.90/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.90/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
% 1.90/1.00      | v1_xboole_0(X0)
% 1.90/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X0)) ),
% 1.90/1.00      inference(renaming,[status(thm)],[c_272]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_340,plain,
% 1.90/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
% 1.90/1.00      | v1_xboole_0(X0)
% 1.90/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X0))
% 1.90/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 1.90/1.00      | sK3 != X0 ),
% 1.90/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_273]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_341,plain,
% 1.90/1.00      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 1.90/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
% 1.90/1.00      | v1_xboole_0(sK3)
% 1.90/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),sK3,k1_tarski(k1_xboole_0)) = k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 1.90/1.00      inference(unflattening,[status(thm)],[c_340]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_343,plain,
% 1.90/1.00      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))),sK3,k1_tarski(k1_xboole_0)) = k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 1.90/1.00      inference(global_propositional_subsumption,
% 1.90/1.00                [status(thm)],
% 1.90/1.00                [c_341,c_19,c_17,c_15]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1394,plain,
% 1.90/1.00      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = k5_xboole_0(sK3,k3_xboole_0(sK3,k1_tarski(k1_xboole_0))) ),
% 1.90/1.00      inference(demodulation,[status(thm)],[c_1379,c_343]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_14,negated_conjecture,
% 1.90/1.00      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != sK3 ),
% 1.90/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1417,plain,
% 1.90/1.00      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k1_tarski(k1_xboole_0))) != sK3 ),
% 1.90/1.00      inference(demodulation,[status(thm)],[c_1394,c_14]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2810,plain,
% 1.90/1.00      ( k5_xboole_0(sK3,k1_xboole_0) != sK3 ),
% 1.90/1.00      inference(demodulation,[status(thm)],[c_2462,c_1417]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_5,plain,
% 1.90/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 1.90/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1250,plain,
% 1.90/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 1.90/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1829,plain,
% 1.90/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.90/1.00      inference(superposition,[status(thm)],[c_1250,c_1822]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_4,plain,
% 1.90/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 1.90/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_1899,plain,
% 1.90/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.90/1.00      inference(demodulation,[status(thm)],[c_1829,c_4]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2816,plain,
% 1.90/1.00      ( sK3 != sK3 ),
% 1.90/1.00      inference(demodulation,[status(thm)],[c_2810,c_1899]) ).
% 1.90/1.00  
% 1.90/1.00  cnf(c_2817,plain,
% 1.90/1.00      ( $false ),
% 1.90/1.00      inference(equality_resolution_simp,[status(thm)],[c_2816]) ).
% 1.90/1.00  
% 1.90/1.00  
% 1.90/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.90/1.00  
% 1.90/1.00  ------                               Statistics
% 1.90/1.00  
% 1.90/1.00  ------ General
% 1.90/1.00  
% 1.90/1.00  abstr_ref_over_cycles:                  0
% 1.90/1.00  abstr_ref_under_cycles:                 0
% 1.90/1.00  gc_basic_clause_elim:                   0
% 1.90/1.00  forced_gc_time:                         0
% 1.90/1.00  parsing_time:                           0.01
% 1.90/1.00  unif_index_cands_time:                  0.
% 1.90/1.00  unif_index_add_time:                    0.
% 1.90/1.00  orderings_time:                         0.
% 1.90/1.00  out_proof_time:                         0.016
% 1.90/1.00  total_time:                             0.13
% 1.90/1.00  num_of_symbols:                         59
% 1.90/1.00  num_of_terms:                           2604
% 1.90/1.00  
% 1.90/1.00  ------ Preprocessing
% 1.90/1.00  
% 1.90/1.00  num_of_splits:                          2
% 1.90/1.00  num_of_split_atoms:                     2
% 1.90/1.00  num_of_reused_defs:                     0
% 1.90/1.00  num_eq_ax_congr_red:                    21
% 1.90/1.00  num_of_sem_filtered_clauses:            1
% 1.90/1.00  num_of_subtypes:                        0
% 1.90/1.00  monotx_restored_types:                  0
% 1.90/1.00  sat_num_of_epr_types:                   0
% 1.90/1.00  sat_num_of_non_cyclic_types:            0
% 1.90/1.00  sat_guarded_non_collapsed_types:        0
% 1.90/1.00  num_pure_diseq_elim:                    0
% 1.90/1.00  simp_replaced_by:                       0
% 1.90/1.00  res_preprocessed:                       107
% 1.90/1.00  prep_upred:                             0
% 1.90/1.00  prep_unflattend:                        41
% 1.90/1.00  smt_new_axioms:                         0
% 1.90/1.00  pred_elim_cands:                        3
% 1.90/1.00  pred_elim:                              6
% 1.90/1.00  pred_elim_cl:                           6
% 1.90/1.00  pred_elim_cycles:                       8
% 1.90/1.00  merged_defs:                            0
% 1.90/1.00  merged_defs_ncl:                        0
% 1.90/1.00  bin_hyper_res:                          0
% 1.90/1.00  prep_cycles:                            4
% 1.90/1.00  pred_elim_time:                         0.015
% 1.90/1.00  splitting_time:                         0.
% 1.90/1.00  sem_filter_time:                        0.
% 1.90/1.00  monotx_time:                            0.001
% 1.90/1.00  subtype_inf_time:                       0.
% 1.90/1.00  
% 1.90/1.00  ------ Problem properties
% 1.90/1.00  
% 1.90/1.00  clauses:                                18
% 1.90/1.00  conjectures:                            2
% 1.90/1.00  epr:                                    6
% 1.90/1.00  horn:                                   14
% 1.90/1.00  ground:                                 6
% 1.90/1.00  unary:                                  7
% 1.90/1.00  binary:                                 7
% 1.90/1.00  lits:                                   35
% 1.90/1.00  lits_eq:                                13
% 1.90/1.00  fd_pure:                                0
% 1.90/1.00  fd_pseudo:                              0
% 1.90/1.00  fd_cond:                                3
% 1.90/1.00  fd_pseudo_cond:                         0
% 1.90/1.00  ac_symbols:                             0
% 1.90/1.00  
% 1.90/1.00  ------ Propositional Solver
% 1.90/1.00  
% 1.90/1.00  prop_solver_calls:                      29
% 1.90/1.00  prop_fast_solver_calls:                 704
% 1.90/1.00  smt_solver_calls:                       0
% 1.90/1.00  smt_fast_solver_calls:                  0
% 1.90/1.00  prop_num_of_clauses:                    945
% 1.90/1.00  prop_preprocess_simplified:             3534
% 1.90/1.00  prop_fo_subsumed:                       19
% 1.90/1.00  prop_solver_time:                       0.
% 1.90/1.00  smt_solver_time:                        0.
% 1.90/1.00  smt_fast_solver_time:                   0.
% 1.90/1.00  prop_fast_solver_time:                  0.
% 1.90/1.00  prop_unsat_core_time:                   0.
% 1.90/1.00  
% 1.90/1.00  ------ QBF
% 1.90/1.00  
% 1.90/1.00  qbf_q_res:                              0
% 1.90/1.00  qbf_num_tautologies:                    0
% 1.90/1.00  qbf_prep_cycles:                        0
% 1.90/1.00  
% 1.90/1.00  ------ BMC1
% 1.90/1.00  
% 1.90/1.00  bmc1_current_bound:                     -1
% 1.90/1.00  bmc1_last_solved_bound:                 -1
% 1.90/1.00  bmc1_unsat_core_size:                   -1
% 1.90/1.00  bmc1_unsat_core_parents_size:           -1
% 1.90/1.00  bmc1_merge_next_fun:                    0
% 1.90/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.90/1.00  
% 1.90/1.00  ------ Instantiation
% 1.90/1.00  
% 1.90/1.00  inst_num_of_clauses:                    325
% 1.90/1.00  inst_num_in_passive:                    118
% 1.90/1.00  inst_num_in_active:                     181
% 1.90/1.00  inst_num_in_unprocessed:                26
% 1.90/1.00  inst_num_of_loops:                      200
% 1.90/1.00  inst_num_of_learning_restarts:          0
% 1.90/1.00  inst_num_moves_active_passive:          15
% 1.90/1.00  inst_lit_activity:                      0
% 1.90/1.00  inst_lit_activity_moves:                0
% 1.90/1.00  inst_num_tautologies:                   0
% 1.90/1.00  inst_num_prop_implied:                  0
% 1.90/1.00  inst_num_existing_simplified:           0
% 1.90/1.00  inst_num_eq_res_simplified:             0
% 1.90/1.00  inst_num_child_elim:                    0
% 1.90/1.00  inst_num_of_dismatching_blockings:      41
% 1.90/1.00  inst_num_of_non_proper_insts:           282
% 1.90/1.00  inst_num_of_duplicates:                 0
% 1.90/1.00  inst_inst_num_from_inst_to_res:         0
% 1.90/1.00  inst_dismatching_checking_time:         0.
% 1.90/1.00  
% 1.90/1.00  ------ Resolution
% 1.90/1.00  
% 1.90/1.00  res_num_of_clauses:                     0
% 1.90/1.00  res_num_in_passive:                     0
% 1.90/1.00  res_num_in_active:                      0
% 1.90/1.00  res_num_of_loops:                       111
% 1.90/1.00  res_forward_subset_subsumed:            59
% 1.90/1.00  res_backward_subset_subsumed:           4
% 1.90/1.00  res_forward_subsumed:                   0
% 1.90/1.00  res_backward_subsumed:                  0
% 1.90/1.00  res_forward_subsumption_resolution:     0
% 1.90/1.00  res_backward_subsumption_resolution:    0
% 1.90/1.00  res_clause_to_clause_subsumption:       169
% 1.90/1.00  res_orphan_elimination:                 0
% 1.90/1.00  res_tautology_del:                      31
% 1.90/1.00  res_num_eq_res_simplified:              1
% 1.90/1.00  res_num_sel_changes:                    0
% 1.90/1.00  res_moves_from_active_to_pass:          0
% 1.90/1.00  
% 1.90/1.00  ------ Superposition
% 1.90/1.00  
% 1.90/1.00  sup_time_total:                         0.
% 1.90/1.00  sup_time_generating:                    0.
% 1.90/1.00  sup_time_sim_full:                      0.
% 1.90/1.00  sup_time_sim_immed:                     0.
% 1.90/1.00  
% 1.90/1.00  sup_num_of_clauses:                     41
% 1.90/1.00  sup_num_in_active:                      33
% 1.90/1.00  sup_num_in_passive:                     8
% 1.90/1.00  sup_num_of_loops:                       38
% 1.90/1.00  sup_fw_superposition:                   20
% 1.90/1.00  sup_bw_superposition:                   22
% 1.90/1.00  sup_immediate_simplified:               11
% 1.90/1.00  sup_given_eliminated:                   0
% 1.90/1.00  comparisons_done:                       0
% 1.90/1.00  comparisons_avoided:                    0
% 1.90/1.00  
% 1.90/1.00  ------ Simplifications
% 1.90/1.00  
% 1.90/1.00  
% 1.90/1.00  sim_fw_subset_subsumed:                 3
% 1.90/1.00  sim_bw_subset_subsumed:                 1
% 1.90/1.00  sim_fw_subsumed:                        1
% 1.90/1.00  sim_bw_subsumed:                        0
% 1.90/1.00  sim_fw_subsumption_res:                 1
% 1.90/1.00  sim_bw_subsumption_res:                 0
% 1.90/1.00  sim_tautology_del:                      1
% 1.90/1.00  sim_eq_tautology_del:                   1
% 1.90/1.00  sim_eq_res_simp:                        0
% 1.90/1.00  sim_fw_demodulated:                     7
% 1.90/1.00  sim_bw_demodulated:                     5
% 1.90/1.00  sim_light_normalised:                   2
% 1.90/1.00  sim_joinable_taut:                      0
% 1.90/1.00  sim_joinable_simp:                      0
% 1.90/1.00  sim_ac_normalised:                      0
% 1.90/1.00  sim_smt_subsumption:                    0
% 1.90/1.00  
%------------------------------------------------------------------------------
