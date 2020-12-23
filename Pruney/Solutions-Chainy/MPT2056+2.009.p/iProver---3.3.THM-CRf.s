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
% DateTime   : Thu Dec  3 12:29:06 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 586 expanded)
%              Number of clauses        :   73 ( 121 expanded)
%              Number of leaves         :   22 ( 172 expanded)
%              Depth                    :   27
%              Number of atoms          :  468 (2813 expanded)
%              Number of equality atoms :  152 ( 601 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f41])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f39])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
    & ~ v1_xboole_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f44,f43])).

fof(f74,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f65,f64])).

fof(f78,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f61,f77])).

fof(f15,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))))) ),
    inference(definition_unfolding,[],[f74,f78,f64])).

fof(f72,plain,(
    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f72,f64])).

fof(f73,plain,(
    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f73,f64])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f67,f78,f64,f64,f64,f64])).

fof(f71,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(definition_unfolding,[],[f71,f64])).

fof(f70,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f57,f52,f78])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f66,f64,f78,f64,f64,f64])).

fof(f75,plain,(
    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f55,f52])).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f53,f76])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f54,f52])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_830,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_827,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_257,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X3,X4))
    | X1 != X4
    | k1_tarski(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_258,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(k1_tarski(X0),X1)) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_824,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X2,k3_xboole_0(k1_tarski(X0),X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_1611,plain,
    ( k3_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_827,c_824])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_20,negated_conjecture,
    ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_19,negated_conjecture,
    ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_16,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_21,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_275,plain,
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

cnf(c_276,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_278,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_276,c_22])).

cnf(c_279,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_360,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_279])).

cnf(c_405,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_360])).

cnf(c_446,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_405])).

cnf(c_491,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_446])).

cnf(c_568,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_491])).

cnf(c_821,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_2002,plain,
    ( k3_xboole_0(k1_tarski(X0),sK4) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1611,c_821])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_312,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_313,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_314,plain,
    ( l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_569,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_491])).

cnf(c_598,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_567,plain,
    ( v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_491])).

cnf(c_822,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_354,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_355,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_901,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(u1_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_822,c_355])).

cnf(c_1004,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))
    | k3_lattice3(k1_lattice3(u1_struct_0(sK3))) != k3_lattice3(k1_lattice3(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_901])).

cnf(c_1290,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1004])).

cnf(c_2047,plain,
    ( v1_xboole_0(X0) != iProver_top
    | k3_xboole_0(k1_tarski(X0),sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2002,c_26,c_314,c_598,c_1290])).

cnf(c_2048,plain,
    ( k3_xboole_0(k1_tarski(X0),sK4) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2047])).

cnf(c_2055,plain,
    ( k3_xboole_0(k1_tarski(k1_xboole_0),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_830,c_2048])).

cnf(c_2114,plain,
    ( k3_xboole_0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2055])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_437,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X2)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_438,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) = k7_subset_1(X1,sK4,X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X1))) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_896,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) = k7_subset_1(X1,sK4,X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X1))) ),
    inference(light_normalisation,[status(thm)],[c_438,c_355])).

cnf(c_976,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))),sK4,X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
    inference(equality_resolution,[status(thm)],[c_896])).

cnf(c_15,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_323,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_324,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | ~ l1_struct_0(sK3)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_23])).

cnf(c_327,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(renaming,[status(thm)],[c_326])).

cnf(c_387,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_327])).

cnf(c_388,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | v1_xboole_0(sK4)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_390,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_22,c_20,c_18])).

cnf(c_877,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) ),
    inference(light_normalisation,[status(thm)],[c_390,c_355])).

cnf(c_1007,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) = k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_976,c_877])).

cnf(c_17,negated_conjecture,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_852,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) != sK4 ),
    inference(light_normalisation,[status(thm)],[c_17,c_355])).

cnf(c_1230,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) != sK4 ),
    inference(demodulation,[status(thm)],[c_1007,c_852])).

cnf(c_2207,plain,
    ( k5_xboole_0(sK4,k1_xboole_0) != sK4 ),
    inference(demodulation,[status(thm)],[c_2114,c_1230])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_7,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_849,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_7])).

cnf(c_2213,plain,
    ( sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_2207,c_849])).

cnf(c_2214,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2213])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.74/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.01  
% 1.74/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.74/1.01  
% 1.74/1.01  ------  iProver source info
% 1.74/1.01  
% 1.74/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.74/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.74/1.01  git: non_committed_changes: false
% 1.74/1.01  git: last_make_outside_of_git: false
% 1.74/1.01  
% 1.74/1.01  ------ 
% 1.74/1.01  
% 1.74/1.01  ------ Input Options
% 1.74/1.01  
% 1.74/1.01  --out_options                           all
% 1.74/1.01  --tptp_safe_out                         true
% 1.74/1.01  --problem_path                          ""
% 1.74/1.01  --include_path                          ""
% 1.74/1.01  --clausifier                            res/vclausify_rel
% 1.74/1.01  --clausifier_options                    --mode clausify
% 1.74/1.01  --stdin                                 false
% 1.74/1.01  --stats_out                             all
% 1.74/1.01  
% 1.74/1.01  ------ General Options
% 1.74/1.01  
% 1.74/1.01  --fof                                   false
% 1.74/1.01  --time_out_real                         305.
% 1.74/1.01  --time_out_virtual                      -1.
% 1.74/1.01  --symbol_type_check                     false
% 1.74/1.01  --clausify_out                          false
% 1.74/1.01  --sig_cnt_out                           false
% 1.74/1.01  --trig_cnt_out                          false
% 1.74/1.01  --trig_cnt_out_tolerance                1.
% 1.74/1.01  --trig_cnt_out_sk_spl                   false
% 1.74/1.01  --abstr_cl_out                          false
% 1.74/1.01  
% 1.74/1.01  ------ Global Options
% 1.74/1.01  
% 1.74/1.01  --schedule                              default
% 1.74/1.01  --add_important_lit                     false
% 1.74/1.01  --prop_solver_per_cl                    1000
% 1.74/1.01  --min_unsat_core                        false
% 1.74/1.01  --soft_assumptions                      false
% 1.74/1.01  --soft_lemma_size                       3
% 1.74/1.01  --prop_impl_unit_size                   0
% 1.74/1.01  --prop_impl_unit                        []
% 1.74/1.01  --share_sel_clauses                     true
% 1.74/1.01  --reset_solvers                         false
% 1.74/1.01  --bc_imp_inh                            [conj_cone]
% 1.74/1.01  --conj_cone_tolerance                   3.
% 1.74/1.01  --extra_neg_conj                        none
% 1.74/1.01  --large_theory_mode                     true
% 1.74/1.01  --prolific_symb_bound                   200
% 1.74/1.01  --lt_threshold                          2000
% 1.74/1.01  --clause_weak_htbl                      true
% 1.74/1.01  --gc_record_bc_elim                     false
% 1.74/1.01  
% 1.74/1.01  ------ Preprocessing Options
% 1.74/1.01  
% 1.74/1.01  --preprocessing_flag                    true
% 1.74/1.01  --time_out_prep_mult                    0.1
% 1.74/1.01  --splitting_mode                        input
% 1.74/1.01  --splitting_grd                         true
% 1.74/1.01  --splitting_cvd                         false
% 1.74/1.01  --splitting_cvd_svl                     false
% 1.74/1.01  --splitting_nvd                         32
% 1.74/1.01  --sub_typing                            true
% 1.74/1.01  --prep_gs_sim                           true
% 1.74/1.01  --prep_unflatten                        true
% 1.74/1.01  --prep_res_sim                          true
% 1.74/1.01  --prep_upred                            true
% 1.74/1.01  --prep_sem_filter                       exhaustive
% 1.74/1.01  --prep_sem_filter_out                   false
% 1.74/1.01  --pred_elim                             true
% 1.74/1.01  --res_sim_input                         true
% 1.74/1.01  --eq_ax_congr_red                       true
% 1.74/1.01  --pure_diseq_elim                       true
% 1.74/1.01  --brand_transform                       false
% 1.74/1.01  --non_eq_to_eq                          false
% 1.74/1.01  --prep_def_merge                        true
% 1.74/1.01  --prep_def_merge_prop_impl              false
% 1.74/1.01  --prep_def_merge_mbd                    true
% 1.74/1.01  --prep_def_merge_tr_red                 false
% 1.74/1.01  --prep_def_merge_tr_cl                  false
% 1.74/1.01  --smt_preprocessing                     true
% 1.74/1.01  --smt_ac_axioms                         fast
% 1.74/1.01  --preprocessed_out                      false
% 1.74/1.01  --preprocessed_stats                    false
% 1.74/1.01  
% 1.74/1.01  ------ Abstraction refinement Options
% 1.74/1.01  
% 1.74/1.01  --abstr_ref                             []
% 1.74/1.01  --abstr_ref_prep                        false
% 1.74/1.01  --abstr_ref_until_sat                   false
% 1.74/1.01  --abstr_ref_sig_restrict                funpre
% 1.74/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.74/1.01  --abstr_ref_under                       []
% 1.74/1.01  
% 1.74/1.01  ------ SAT Options
% 1.74/1.01  
% 1.74/1.01  --sat_mode                              false
% 1.74/1.01  --sat_fm_restart_options                ""
% 1.74/1.01  --sat_gr_def                            false
% 1.74/1.01  --sat_epr_types                         true
% 1.74/1.01  --sat_non_cyclic_types                  false
% 1.74/1.01  --sat_finite_models                     false
% 1.74/1.01  --sat_fm_lemmas                         false
% 1.74/1.01  --sat_fm_prep                           false
% 1.74/1.01  --sat_fm_uc_incr                        true
% 1.74/1.01  --sat_out_model                         small
% 1.74/1.01  --sat_out_clauses                       false
% 1.74/1.01  
% 1.74/1.01  ------ QBF Options
% 1.74/1.01  
% 1.74/1.01  --qbf_mode                              false
% 1.74/1.01  --qbf_elim_univ                         false
% 1.74/1.01  --qbf_dom_inst                          none
% 1.74/1.01  --qbf_dom_pre_inst                      false
% 1.74/1.01  --qbf_sk_in                             false
% 1.74/1.01  --qbf_pred_elim                         true
% 1.74/1.01  --qbf_split                             512
% 1.74/1.01  
% 1.74/1.01  ------ BMC1 Options
% 1.74/1.01  
% 1.74/1.01  --bmc1_incremental                      false
% 1.74/1.01  --bmc1_axioms                           reachable_all
% 1.74/1.01  --bmc1_min_bound                        0
% 1.74/1.01  --bmc1_max_bound                        -1
% 1.74/1.01  --bmc1_max_bound_default                -1
% 1.74/1.01  --bmc1_symbol_reachability              true
% 1.74/1.01  --bmc1_property_lemmas                  false
% 1.74/1.01  --bmc1_k_induction                      false
% 1.74/1.01  --bmc1_non_equiv_states                 false
% 1.74/1.01  --bmc1_deadlock                         false
% 1.74/1.01  --bmc1_ucm                              false
% 1.74/1.01  --bmc1_add_unsat_core                   none
% 1.74/1.01  --bmc1_unsat_core_children              false
% 1.74/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.74/1.01  --bmc1_out_stat                         full
% 1.74/1.01  --bmc1_ground_init                      false
% 1.74/1.01  --bmc1_pre_inst_next_state              false
% 1.74/1.01  --bmc1_pre_inst_state                   false
% 1.74/1.01  --bmc1_pre_inst_reach_state             false
% 1.74/1.01  --bmc1_out_unsat_core                   false
% 1.74/1.01  --bmc1_aig_witness_out                  false
% 1.74/1.01  --bmc1_verbose                          false
% 1.74/1.01  --bmc1_dump_clauses_tptp                false
% 1.74/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.74/1.01  --bmc1_dump_file                        -
% 1.74/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.74/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.74/1.01  --bmc1_ucm_extend_mode                  1
% 1.74/1.01  --bmc1_ucm_init_mode                    2
% 1.74/1.01  --bmc1_ucm_cone_mode                    none
% 1.74/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.74/1.01  --bmc1_ucm_relax_model                  4
% 1.74/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.74/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.74/1.01  --bmc1_ucm_layered_model                none
% 1.74/1.01  --bmc1_ucm_max_lemma_size               10
% 1.74/1.01  
% 1.74/1.01  ------ AIG Options
% 1.74/1.01  
% 1.74/1.01  --aig_mode                              false
% 1.74/1.01  
% 1.74/1.01  ------ Instantiation Options
% 1.74/1.01  
% 1.74/1.01  --instantiation_flag                    true
% 1.74/1.01  --inst_sos_flag                         false
% 1.74/1.01  --inst_sos_phase                        true
% 1.74/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.74/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.74/1.01  --inst_lit_sel_side                     num_symb
% 1.74/1.01  --inst_solver_per_active                1400
% 1.74/1.01  --inst_solver_calls_frac                1.
% 1.74/1.01  --inst_passive_queue_type               priority_queues
% 1.74/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.74/1.01  --inst_passive_queues_freq              [25;2]
% 1.74/1.01  --inst_dismatching                      true
% 1.74/1.01  --inst_eager_unprocessed_to_passive     true
% 1.74/1.01  --inst_prop_sim_given                   true
% 1.74/1.01  --inst_prop_sim_new                     false
% 1.74/1.01  --inst_subs_new                         false
% 1.74/1.01  --inst_eq_res_simp                      false
% 1.74/1.01  --inst_subs_given                       false
% 1.74/1.01  --inst_orphan_elimination               true
% 1.74/1.01  --inst_learning_loop_flag               true
% 1.74/1.01  --inst_learning_start                   3000
% 1.74/1.01  --inst_learning_factor                  2
% 1.74/1.01  --inst_start_prop_sim_after_learn       3
% 1.74/1.01  --inst_sel_renew                        solver
% 1.74/1.01  --inst_lit_activity_flag                true
% 1.74/1.01  --inst_restr_to_given                   false
% 1.74/1.01  --inst_activity_threshold               500
% 1.74/1.01  --inst_out_proof                        true
% 1.74/1.01  
% 1.74/1.01  ------ Resolution Options
% 1.74/1.01  
% 1.74/1.01  --resolution_flag                       true
% 1.74/1.01  --res_lit_sel                           adaptive
% 1.74/1.01  --res_lit_sel_side                      none
% 1.74/1.01  --res_ordering                          kbo
% 1.74/1.01  --res_to_prop_solver                    active
% 1.74/1.01  --res_prop_simpl_new                    false
% 1.74/1.01  --res_prop_simpl_given                  true
% 1.74/1.01  --res_passive_queue_type                priority_queues
% 1.74/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.74/1.01  --res_passive_queues_freq               [15;5]
% 1.74/1.01  --res_forward_subs                      full
% 1.74/1.01  --res_backward_subs                     full
% 1.74/1.01  --res_forward_subs_resolution           true
% 1.74/1.01  --res_backward_subs_resolution          true
% 1.74/1.01  --res_orphan_elimination                true
% 1.74/1.01  --res_time_limit                        2.
% 1.74/1.01  --res_out_proof                         true
% 1.74/1.01  
% 1.74/1.01  ------ Superposition Options
% 1.74/1.01  
% 1.74/1.01  --superposition_flag                    true
% 1.74/1.01  --sup_passive_queue_type                priority_queues
% 1.74/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.74/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.74/1.01  --demod_completeness_check              fast
% 1.74/1.01  --demod_use_ground                      true
% 1.74/1.01  --sup_to_prop_solver                    passive
% 1.74/1.01  --sup_prop_simpl_new                    true
% 1.74/1.01  --sup_prop_simpl_given                  true
% 1.74/1.01  --sup_fun_splitting                     false
% 1.74/1.01  --sup_smt_interval                      50000
% 1.74/1.01  
% 1.74/1.01  ------ Superposition Simplification Setup
% 1.74/1.01  
% 1.74/1.01  --sup_indices_passive                   []
% 1.74/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.74/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.01  --sup_full_bw                           [BwDemod]
% 1.74/1.01  --sup_immed_triv                        [TrivRules]
% 1.74/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.74/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.01  --sup_immed_bw_main                     []
% 1.74/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.74/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.74/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.74/1.01  
% 1.74/1.01  ------ Combination Options
% 1.74/1.01  
% 1.74/1.01  --comb_res_mult                         3
% 1.74/1.01  --comb_sup_mult                         2
% 1.74/1.01  --comb_inst_mult                        10
% 1.74/1.01  
% 1.74/1.01  ------ Debug Options
% 1.74/1.01  
% 1.74/1.01  --dbg_backtrace                         false
% 1.74/1.01  --dbg_dump_prop_clauses                 false
% 1.74/1.01  --dbg_dump_prop_clauses_file            -
% 1.74/1.01  --dbg_out_stat                          false
% 1.74/1.01  ------ Parsing...
% 1.74/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.74/1.01  
% 1.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.74/1.01  
% 1.74/1.01  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.74/1.01  
% 1.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.74/1.01  ------ Proving...
% 1.74/1.01  ------ Problem Properties 
% 1.74/1.01  
% 1.74/1.01  
% 1.74/1.01  clauses                                 20
% 1.74/1.01  conjectures                             2
% 1.74/1.01  EPR                                     5
% 1.74/1.01  Horn                                    17
% 1.74/1.01  unary                                   9
% 1.74/1.01  binary                                  7
% 1.74/1.01  lits                                    37
% 1.74/1.01  lits eq                                 16
% 1.74/1.01  fd_pure                                 0
% 1.74/1.01  fd_pseudo                               0
% 1.74/1.01  fd_cond                                 3
% 1.74/1.01  fd_pseudo_cond                          0
% 1.74/1.01  AC symbols                              0
% 1.74/1.01  
% 1.74/1.01  ------ Schedule dynamic 5 is on 
% 1.74/1.01  
% 1.74/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.74/1.01  
% 1.74/1.01  
% 1.74/1.01  ------ 
% 1.74/1.01  Current options:
% 1.74/1.01  ------ 
% 1.74/1.01  
% 1.74/1.01  ------ Input Options
% 1.74/1.01  
% 1.74/1.01  --out_options                           all
% 1.74/1.01  --tptp_safe_out                         true
% 1.74/1.01  --problem_path                          ""
% 1.74/1.01  --include_path                          ""
% 1.74/1.01  --clausifier                            res/vclausify_rel
% 1.74/1.01  --clausifier_options                    --mode clausify
% 1.74/1.01  --stdin                                 false
% 1.74/1.01  --stats_out                             all
% 1.74/1.01  
% 1.74/1.01  ------ General Options
% 1.74/1.01  
% 1.74/1.01  --fof                                   false
% 1.74/1.01  --time_out_real                         305.
% 1.74/1.01  --time_out_virtual                      -1.
% 1.74/1.01  --symbol_type_check                     false
% 1.74/1.01  --clausify_out                          false
% 1.74/1.01  --sig_cnt_out                           false
% 1.74/1.01  --trig_cnt_out                          false
% 1.74/1.01  --trig_cnt_out_tolerance                1.
% 1.74/1.01  --trig_cnt_out_sk_spl                   false
% 1.74/1.01  --abstr_cl_out                          false
% 1.74/1.01  
% 1.74/1.01  ------ Global Options
% 1.74/1.01  
% 1.74/1.01  --schedule                              default
% 1.74/1.01  --add_important_lit                     false
% 1.74/1.01  --prop_solver_per_cl                    1000
% 1.74/1.01  --min_unsat_core                        false
% 1.74/1.01  --soft_assumptions                      false
% 1.74/1.01  --soft_lemma_size                       3
% 1.74/1.01  --prop_impl_unit_size                   0
% 1.74/1.01  --prop_impl_unit                        []
% 1.74/1.01  --share_sel_clauses                     true
% 1.74/1.01  --reset_solvers                         false
% 1.74/1.01  --bc_imp_inh                            [conj_cone]
% 1.74/1.01  --conj_cone_tolerance                   3.
% 1.74/1.01  --extra_neg_conj                        none
% 1.74/1.01  --large_theory_mode                     true
% 1.74/1.01  --prolific_symb_bound                   200
% 1.74/1.01  --lt_threshold                          2000
% 1.74/1.01  --clause_weak_htbl                      true
% 1.74/1.01  --gc_record_bc_elim                     false
% 1.74/1.01  
% 1.74/1.01  ------ Preprocessing Options
% 1.74/1.01  
% 1.74/1.01  --preprocessing_flag                    true
% 1.74/1.01  --time_out_prep_mult                    0.1
% 1.74/1.01  --splitting_mode                        input
% 1.74/1.01  --splitting_grd                         true
% 1.74/1.01  --splitting_cvd                         false
% 1.74/1.01  --splitting_cvd_svl                     false
% 1.74/1.01  --splitting_nvd                         32
% 1.74/1.01  --sub_typing                            true
% 1.74/1.01  --prep_gs_sim                           true
% 1.74/1.01  --prep_unflatten                        true
% 1.74/1.01  --prep_res_sim                          true
% 1.74/1.01  --prep_upred                            true
% 1.74/1.01  --prep_sem_filter                       exhaustive
% 1.74/1.01  --prep_sem_filter_out                   false
% 1.74/1.01  --pred_elim                             true
% 1.74/1.01  --res_sim_input                         true
% 1.74/1.01  --eq_ax_congr_red                       true
% 1.74/1.01  --pure_diseq_elim                       true
% 1.74/1.01  --brand_transform                       false
% 1.74/1.01  --non_eq_to_eq                          false
% 1.74/1.01  --prep_def_merge                        true
% 1.74/1.01  --prep_def_merge_prop_impl              false
% 1.74/1.01  --prep_def_merge_mbd                    true
% 1.74/1.01  --prep_def_merge_tr_red                 false
% 1.74/1.01  --prep_def_merge_tr_cl                  false
% 1.74/1.01  --smt_preprocessing                     true
% 1.74/1.01  --smt_ac_axioms                         fast
% 1.74/1.01  --preprocessed_out                      false
% 1.74/1.01  --preprocessed_stats                    false
% 1.74/1.01  
% 1.74/1.01  ------ Abstraction refinement Options
% 1.74/1.01  
% 1.74/1.01  --abstr_ref                             []
% 1.74/1.01  --abstr_ref_prep                        false
% 1.74/1.01  --abstr_ref_until_sat                   false
% 1.74/1.01  --abstr_ref_sig_restrict                funpre
% 1.74/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.74/1.01  --abstr_ref_under                       []
% 1.74/1.01  
% 1.74/1.01  ------ SAT Options
% 1.74/1.01  
% 1.74/1.01  --sat_mode                              false
% 1.74/1.01  --sat_fm_restart_options                ""
% 1.74/1.01  --sat_gr_def                            false
% 1.74/1.01  --sat_epr_types                         true
% 1.74/1.01  --sat_non_cyclic_types                  false
% 1.74/1.01  --sat_finite_models                     false
% 1.74/1.01  --sat_fm_lemmas                         false
% 1.74/1.01  --sat_fm_prep                           false
% 1.74/1.01  --sat_fm_uc_incr                        true
% 1.74/1.01  --sat_out_model                         small
% 1.74/1.01  --sat_out_clauses                       false
% 1.74/1.01  
% 1.74/1.01  ------ QBF Options
% 1.74/1.01  
% 1.74/1.01  --qbf_mode                              false
% 1.74/1.01  --qbf_elim_univ                         false
% 1.74/1.01  --qbf_dom_inst                          none
% 1.74/1.01  --qbf_dom_pre_inst                      false
% 1.74/1.01  --qbf_sk_in                             false
% 1.74/1.01  --qbf_pred_elim                         true
% 1.74/1.01  --qbf_split                             512
% 1.74/1.01  
% 1.74/1.01  ------ BMC1 Options
% 1.74/1.01  
% 1.74/1.01  --bmc1_incremental                      false
% 1.74/1.01  --bmc1_axioms                           reachable_all
% 1.74/1.01  --bmc1_min_bound                        0
% 1.74/1.01  --bmc1_max_bound                        -1
% 1.74/1.01  --bmc1_max_bound_default                -1
% 1.74/1.01  --bmc1_symbol_reachability              true
% 1.74/1.01  --bmc1_property_lemmas                  false
% 1.74/1.01  --bmc1_k_induction                      false
% 1.74/1.01  --bmc1_non_equiv_states                 false
% 1.74/1.01  --bmc1_deadlock                         false
% 1.74/1.01  --bmc1_ucm                              false
% 1.74/1.01  --bmc1_add_unsat_core                   none
% 1.74/1.01  --bmc1_unsat_core_children              false
% 1.74/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.74/1.01  --bmc1_out_stat                         full
% 1.74/1.01  --bmc1_ground_init                      false
% 1.74/1.01  --bmc1_pre_inst_next_state              false
% 1.74/1.01  --bmc1_pre_inst_state                   false
% 1.74/1.01  --bmc1_pre_inst_reach_state             false
% 1.74/1.01  --bmc1_out_unsat_core                   false
% 1.74/1.01  --bmc1_aig_witness_out                  false
% 1.74/1.01  --bmc1_verbose                          false
% 1.74/1.01  --bmc1_dump_clauses_tptp                false
% 1.74/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.74/1.01  --bmc1_dump_file                        -
% 1.74/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.74/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.74/1.01  --bmc1_ucm_extend_mode                  1
% 1.74/1.01  --bmc1_ucm_init_mode                    2
% 1.74/1.01  --bmc1_ucm_cone_mode                    none
% 1.74/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.74/1.01  --bmc1_ucm_relax_model                  4
% 1.74/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.74/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.74/1.01  --bmc1_ucm_layered_model                none
% 1.74/1.01  --bmc1_ucm_max_lemma_size               10
% 1.74/1.01  
% 1.74/1.01  ------ AIG Options
% 1.74/1.01  
% 1.74/1.01  --aig_mode                              false
% 1.74/1.01  
% 1.74/1.01  ------ Instantiation Options
% 1.74/1.01  
% 1.74/1.01  --instantiation_flag                    true
% 1.74/1.01  --inst_sos_flag                         false
% 1.74/1.01  --inst_sos_phase                        true
% 1.74/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.74/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.74/1.01  --inst_lit_sel_side                     none
% 1.74/1.01  --inst_solver_per_active                1400
% 1.74/1.01  --inst_solver_calls_frac                1.
% 1.74/1.01  --inst_passive_queue_type               priority_queues
% 1.74/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.74/1.01  --inst_passive_queues_freq              [25;2]
% 1.74/1.01  --inst_dismatching                      true
% 1.74/1.01  --inst_eager_unprocessed_to_passive     true
% 1.74/1.01  --inst_prop_sim_given                   true
% 1.74/1.01  --inst_prop_sim_new                     false
% 1.74/1.01  --inst_subs_new                         false
% 1.74/1.01  --inst_eq_res_simp                      false
% 1.74/1.01  --inst_subs_given                       false
% 1.74/1.01  --inst_orphan_elimination               true
% 1.74/1.01  --inst_learning_loop_flag               true
% 1.74/1.01  --inst_learning_start                   3000
% 1.74/1.01  --inst_learning_factor                  2
% 1.74/1.01  --inst_start_prop_sim_after_learn       3
% 1.74/1.01  --inst_sel_renew                        solver
% 1.74/1.01  --inst_lit_activity_flag                true
% 1.74/1.01  --inst_restr_to_given                   false
% 1.74/1.01  --inst_activity_threshold               500
% 1.74/1.01  --inst_out_proof                        true
% 1.74/1.01  
% 1.74/1.01  ------ Resolution Options
% 1.74/1.01  
% 1.74/1.01  --resolution_flag                       false
% 1.74/1.01  --res_lit_sel                           adaptive
% 1.74/1.01  --res_lit_sel_side                      none
% 1.74/1.01  --res_ordering                          kbo
% 1.74/1.01  --res_to_prop_solver                    active
% 1.74/1.01  --res_prop_simpl_new                    false
% 1.74/1.01  --res_prop_simpl_given                  true
% 1.74/1.01  --res_passive_queue_type                priority_queues
% 1.74/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.74/1.01  --res_passive_queues_freq               [15;5]
% 1.74/1.01  --res_forward_subs                      full
% 1.74/1.01  --res_backward_subs                     full
% 1.74/1.01  --res_forward_subs_resolution           true
% 1.74/1.01  --res_backward_subs_resolution          true
% 1.74/1.01  --res_orphan_elimination                true
% 1.74/1.01  --res_time_limit                        2.
% 1.74/1.01  --res_out_proof                         true
% 1.74/1.01  
% 1.74/1.01  ------ Superposition Options
% 1.74/1.01  
% 1.74/1.01  --superposition_flag                    true
% 1.74/1.01  --sup_passive_queue_type                priority_queues
% 1.74/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.74/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.74/1.01  --demod_completeness_check              fast
% 1.74/1.01  --demod_use_ground                      true
% 1.74/1.01  --sup_to_prop_solver                    passive
% 1.74/1.01  --sup_prop_simpl_new                    true
% 1.74/1.01  --sup_prop_simpl_given                  true
% 1.74/1.01  --sup_fun_splitting                     false
% 1.74/1.01  --sup_smt_interval                      50000
% 1.74/1.01  
% 1.74/1.01  ------ Superposition Simplification Setup
% 1.74/1.01  
% 1.74/1.01  --sup_indices_passive                   []
% 1.74/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.74/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.01  --sup_full_bw                           [BwDemod]
% 1.74/1.01  --sup_immed_triv                        [TrivRules]
% 1.74/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.74/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.01  --sup_immed_bw_main                     []
% 1.74/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.74/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.74/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.74/1.01  
% 1.74/1.01  ------ Combination Options
% 1.74/1.01  
% 1.74/1.01  --comb_res_mult                         3
% 1.74/1.01  --comb_sup_mult                         2
% 1.74/1.01  --comb_inst_mult                        10
% 1.74/1.01  
% 1.74/1.01  ------ Debug Options
% 1.74/1.01  
% 1.74/1.01  --dbg_backtrace                         false
% 1.74/1.01  --dbg_dump_prop_clauses                 false
% 1.74/1.01  --dbg_dump_prop_clauses_file            -
% 1.74/1.01  --dbg_out_stat                          false
% 1.74/1.01  
% 1.74/1.01  
% 1.74/1.01  
% 1.74/1.01  
% 1.74/1.01  ------ Proving...
% 1.74/1.01  
% 1.74/1.01  
% 1.74/1.01  % SZS status Theorem for theBenchmark.p
% 1.74/1.01  
% 1.74/1.01   Resolution empty clause
% 1.74/1.01  
% 1.74/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.74/1.01  
% 1.74/1.01  fof(f1,axiom,(
% 1.74/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f46,plain,(
% 1.74/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.74/1.01    inference(cnf_transformation,[],[f1])).
% 1.74/1.01  
% 1.74/1.01  fof(f3,axiom,(
% 1.74/1.01    v1_xboole_0(k1_xboole_0)),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f49,plain,(
% 1.74/1.01    v1_xboole_0(k1_xboole_0)),
% 1.74/1.01    inference(cnf_transformation,[],[f3])).
% 1.74/1.01  
% 1.74/1.01  fof(f11,axiom,(
% 1.74/1.01    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f25,plain,(
% 1.74/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.74/1.01    inference(ennf_transformation,[],[f11])).
% 1.74/1.01  
% 1.74/1.01  fof(f41,plain,(
% 1.74/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 1.74/1.01    introduced(choice_axiom,[])).
% 1.74/1.01  
% 1.74/1.01  fof(f42,plain,(
% 1.74/1.01    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 1.74/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f41])).
% 1.74/1.01  
% 1.74/1.01  fof(f58,plain,(
% 1.74/1.01    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.74/1.01    inference(cnf_transformation,[],[f42])).
% 1.74/1.01  
% 1.74/1.01  fof(f4,axiom,(
% 1.74/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f21,plain,(
% 1.74/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.74/1.01    inference(rectify,[],[f4])).
% 1.74/1.01  
% 1.74/1.01  fof(f22,plain,(
% 1.74/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.74/1.01    inference(ennf_transformation,[],[f21])).
% 1.74/1.01  
% 1.74/1.01  fof(f39,plain,(
% 1.74/1.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 1.74/1.01    introduced(choice_axiom,[])).
% 1.74/1.01  
% 1.74/1.01  fof(f40,plain,(
% 1.74/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.74/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f39])).
% 1.74/1.01  
% 1.74/1.01  fof(f51,plain,(
% 1.74/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.74/1.01    inference(cnf_transformation,[],[f40])).
% 1.74/1.01  
% 1.74/1.01  fof(f9,axiom,(
% 1.74/1.01    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f23,plain,(
% 1.74/1.01    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.74/1.01    inference(ennf_transformation,[],[f9])).
% 1.74/1.01  
% 1.74/1.01  fof(f56,plain,(
% 1.74/1.01    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.74/1.01    inference(cnf_transformation,[],[f23])).
% 1.74/1.01  
% 1.74/1.01  fof(f19,conjecture,(
% 1.74/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f20,negated_conjecture,(
% 1.74/1.01    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.74/1.01    inference(negated_conjecture,[],[f19])).
% 1.74/1.01  
% 1.74/1.01  fof(f33,plain,(
% 1.74/1.01    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.74/1.01    inference(ennf_transformation,[],[f20])).
% 1.74/1.01  
% 1.74/1.01  fof(f34,plain,(
% 1.74/1.01    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.74/1.01    inference(flattening,[],[f33])).
% 1.74/1.01  
% 1.74/1.01  fof(f44,plain,(
% 1.74/1.01    ( ! [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK4))) )),
% 1.74/1.01    introduced(choice_axiom,[])).
% 1.74/1.01  
% 1.74/1.01  fof(f43,plain,(
% 1.74/1.01    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 1.74/1.01    introduced(choice_axiom,[])).
% 1.74/1.01  
% 1.74/1.01  fof(f45,plain,(
% 1.74/1.01    (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 1.74/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f44,f43])).
% 1.74/1.01  
% 1.74/1.01  fof(f74,plain,(
% 1.74/1.01    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))),
% 1.74/1.01    inference(cnf_transformation,[],[f45])).
% 1.74/1.01  
% 1.74/1.01  fof(f12,axiom,(
% 1.74/1.01    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f61,plain,(
% 1.74/1.01    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 1.74/1.01    inference(cnf_transformation,[],[f12])).
% 1.74/1.01  
% 1.74/1.01  fof(f16,axiom,(
% 1.74/1.01    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f65,plain,(
% 1.74/1.01    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 1.74/1.01    inference(cnf_transformation,[],[f16])).
% 1.74/1.01  
% 1.74/1.01  fof(f77,plain,(
% 1.74/1.01    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 1.74/1.01    inference(definition_unfolding,[],[f65,f64])).
% 1.74/1.01  
% 1.74/1.01  fof(f78,plain,(
% 1.74/1.01    ( ! [X0] : (k1_zfmisc_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 1.74/1.01    inference(definition_unfolding,[],[f61,f77])).
% 1.74/1.01  
% 1.74/1.01  fof(f15,axiom,(
% 1.74/1.01    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f64,plain,(
% 1.74/1.01    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.74/1.01    inference(cnf_transformation,[],[f15])).
% 1.74/1.01  
% 1.74/1.01  fof(f84,plain,(
% 1.74/1.01    m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))),
% 1.74/1.01    inference(definition_unfolding,[],[f74,f78,f64])).
% 1.74/1.01  
% 1.74/1.01  fof(f72,plain,(
% 1.74/1.01    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 1.74/1.01    inference(cnf_transformation,[],[f45])).
% 1.74/1.01  
% 1.74/1.01  fof(f86,plain,(
% 1.74/1.01    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 1.74/1.01    inference(definition_unfolding,[],[f72,f64])).
% 1.74/1.01  
% 1.74/1.01  fof(f73,plain,(
% 1.74/1.01    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 1.74/1.01    inference(cnf_transformation,[],[f45])).
% 1.74/1.01  
% 1.74/1.01  fof(f85,plain,(
% 1.74/1.01    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 1.74/1.01    inference(definition_unfolding,[],[f73,f64])).
% 1.74/1.01  
% 1.74/1.01  fof(f18,axiom,(
% 1.74/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f31,plain,(
% 1.74/1.01    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.74/1.01    inference(ennf_transformation,[],[f18])).
% 1.74/1.01  
% 1.74/1.01  fof(f32,plain,(
% 1.74/1.01    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.74/1.01    inference(flattening,[],[f31])).
% 1.74/1.01  
% 1.74/1.01  fof(f67,plain,(
% 1.74/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.74/1.01    inference(cnf_transformation,[],[f32])).
% 1.74/1.01  
% 1.74/1.01  fof(f83,plain,(
% 1.74/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.74/1.01    inference(definition_unfolding,[],[f67,f78,f64,f64,f64,f64])).
% 1.74/1.01  
% 1.74/1.01  fof(f71,plain,(
% 1.74/1.01    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))),
% 1.74/1.01    inference(cnf_transformation,[],[f45])).
% 1.74/1.01  
% 1.74/1.01  fof(f87,plain,(
% 1.74/1.01    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))),
% 1.74/1.01    inference(definition_unfolding,[],[f71,f64])).
% 1.74/1.01  
% 1.74/1.01  fof(f70,plain,(
% 1.74/1.01    ~v1_xboole_0(sK4)),
% 1.74/1.01    inference(cnf_transformation,[],[f45])).
% 1.74/1.01  
% 1.74/1.01  fof(f69,plain,(
% 1.74/1.01    l1_struct_0(sK3)),
% 1.74/1.01    inference(cnf_transformation,[],[f45])).
% 1.74/1.01  
% 1.74/1.01  fof(f14,axiom,(
% 1.74/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f27,plain,(
% 1.74/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.74/1.01    inference(ennf_transformation,[],[f14])).
% 1.74/1.01  
% 1.74/1.01  fof(f28,plain,(
% 1.74/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.74/1.01    inference(flattening,[],[f27])).
% 1.74/1.01  
% 1.74/1.01  fof(f63,plain,(
% 1.74/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.01    inference(cnf_transformation,[],[f28])).
% 1.74/1.01  
% 1.74/1.01  fof(f68,plain,(
% 1.74/1.01    ~v2_struct_0(sK3)),
% 1.74/1.01    inference(cnf_transformation,[],[f45])).
% 1.74/1.01  
% 1.74/1.01  fof(f13,axiom,(
% 1.74/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f26,plain,(
% 1.74/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.74/1.01    inference(ennf_transformation,[],[f13])).
% 1.74/1.01  
% 1.74/1.01  fof(f62,plain,(
% 1.74/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.74/1.01    inference(cnf_transformation,[],[f26])).
% 1.74/1.01  
% 1.74/1.01  fof(f10,axiom,(
% 1.74/1.01    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f24,plain,(
% 1.74/1.01    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.74/1.01    inference(ennf_transformation,[],[f10])).
% 1.74/1.01  
% 1.74/1.01  fof(f57,plain,(
% 1.74/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.74/1.01    inference(cnf_transformation,[],[f24])).
% 1.74/1.01  
% 1.74/1.01  fof(f5,axiom,(
% 1.74/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f52,plain,(
% 1.74/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.74/1.01    inference(cnf_transformation,[],[f5])).
% 1.74/1.01  
% 1.74/1.01  fof(f81,plain,(
% 1.74/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 1.74/1.01    inference(definition_unfolding,[],[f57,f52,f78])).
% 1.74/1.01  
% 1.74/1.01  fof(f17,axiom,(
% 1.74/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f29,plain,(
% 1.74/1.01    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.74/1.01    inference(ennf_transformation,[],[f17])).
% 1.74/1.01  
% 1.74/1.01  fof(f30,plain,(
% 1.74/1.01    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.74/1.01    inference(flattening,[],[f29])).
% 1.74/1.01  
% 1.74/1.01  fof(f66,plain,(
% 1.74/1.01    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.01    inference(cnf_transformation,[],[f30])).
% 1.74/1.01  
% 1.74/1.01  fof(f82,plain,(
% 1.74/1.01    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.01    inference(definition_unfolding,[],[f66,f64,f78,f64,f64,f64])).
% 1.74/1.01  
% 1.74/1.01  fof(f75,plain,(
% 1.74/1.01    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4),
% 1.74/1.01    inference(cnf_transformation,[],[f45])).
% 1.74/1.01  
% 1.74/1.01  fof(f6,axiom,(
% 1.74/1.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f53,plain,(
% 1.74/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.74/1.01    inference(cnf_transformation,[],[f6])).
% 1.74/1.01  
% 1.74/1.01  fof(f8,axiom,(
% 1.74/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f55,plain,(
% 1.74/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.74/1.01    inference(cnf_transformation,[],[f8])).
% 1.74/1.01  
% 1.74/1.01  fof(f76,plain,(
% 1.74/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 1.74/1.01    inference(definition_unfolding,[],[f55,f52])).
% 1.74/1.01  
% 1.74/1.01  fof(f79,plain,(
% 1.74/1.01    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 1.74/1.01    inference(definition_unfolding,[],[f53,f76])).
% 1.74/1.01  
% 1.74/1.01  fof(f7,axiom,(
% 1.74/1.01    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f54,plain,(
% 1.74/1.01    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.74/1.01    inference(cnf_transformation,[],[f7])).
% 1.74/1.01  
% 1.74/1.01  fof(f80,plain,(
% 1.74/1.01    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.74/1.01    inference(definition_unfolding,[],[f54,f52])).
% 1.74/1.01  
% 1.74/1.01  cnf(c_0,plain,
% 1.74/1.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 1.74/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_3,plain,
% 1.74/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 1.74/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_830,plain,
% 1.74/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.74/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_12,plain,
% 1.74/1.01      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 1.74/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_827,plain,
% 1.74/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 1.74/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_4,plain,
% 1.74/1.01      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 1.74/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_8,plain,
% 1.74/1.01      ( r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 1.74/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_257,plain,
% 1.74/1.01      ( r2_hidden(X0,X1)
% 1.74/1.01      | ~ r2_hidden(X2,k3_xboole_0(X3,X4))
% 1.74/1.01      | X1 != X4
% 1.74/1.01      | k1_tarski(X0) != X3 ),
% 1.74/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_8]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_258,plain,
% 1.74/1.01      ( r2_hidden(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(k1_tarski(X0),X1)) ),
% 1.74/1.01      inference(unflattening,[status(thm)],[c_257]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_824,plain,
% 1.74/1.01      ( r2_hidden(X0,X1) = iProver_top
% 1.74/1.01      | r2_hidden(X2,k3_xboole_0(k1_tarski(X0),X1)) != iProver_top ),
% 1.74/1.01      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_1611,plain,
% 1.74/1.01      ( k3_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
% 1.74/1.01      | r2_hidden(X0,X1) = iProver_top ),
% 1.74/1.01      inference(superposition,[status(thm)],[c_827,c_824]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_18,negated_conjecture,
% 1.74/1.01      ( m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))))) ),
% 1.74/1.01      inference(cnf_transformation,[],[f84]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_20,negated_conjecture,
% 1.74/1.01      ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 1.74/1.01      inference(cnf_transformation,[],[f86]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_19,negated_conjecture,
% 1.74/1.01      ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 1.74/1.01      inference(cnf_transformation,[],[f85]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_16,plain,
% 1.74/1.01      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.74/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.01      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))
% 1.74/1.01      | ~ r2_hidden(X2,X0)
% 1.74/1.01      | ~ v1_xboole_0(X2)
% 1.74/1.01      | v1_xboole_0(X1)
% 1.74/1.01      | v1_xboole_0(X0) ),
% 1.74/1.01      inference(cnf_transformation,[],[f83]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_21,negated_conjecture,
% 1.74/1.01      ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
% 1.74/1.01      inference(cnf_transformation,[],[f87]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_275,plain,
% 1.74/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.01      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))
% 1.74/1.01      | ~ r2_hidden(X2,X0)
% 1.74/1.01      | ~ v1_xboole_0(X2)
% 1.74/1.01      | v1_xboole_0(X0)
% 1.74/1.01      | v1_xboole_0(X1)
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.74/1.01      | sK4 != X0 ),
% 1.74/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_276,plain,
% 1.74/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.01      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 1.74/1.01      | ~ r2_hidden(X1,sK4)
% 1.74/1.01      | ~ v1_xboole_0(X1)
% 1.74/1.01      | v1_xboole_0(X0)
% 1.74/1.01      | v1_xboole_0(sK4)
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.74/1.01      inference(unflattening,[status(thm)],[c_275]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_22,negated_conjecture,
% 1.74/1.01      ( ~ v1_xboole_0(sK4) ),
% 1.74/1.01      inference(cnf_transformation,[],[f70]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_278,plain,
% 1.74/1.01      ( v1_xboole_0(X0)
% 1.74/1.01      | ~ v1_xboole_0(X1)
% 1.74/1.01      | ~ r2_hidden(X1,sK4)
% 1.74/1.01      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 1.74/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.01      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.74/1.01      inference(global_propositional_subsumption,[status(thm)],[c_276,c_22]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_279,plain,
% 1.74/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.01      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.01      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 1.74/1.01      | ~ r2_hidden(X1,sK4)
% 1.74/1.01      | ~ v1_xboole_0(X1)
% 1.74/1.01      | v1_xboole_0(X0)
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.74/1.01      inference(renaming,[status(thm)],[c_278]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_360,plain,
% 1.74/1.01      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.01      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 1.74/1.01      | ~ r2_hidden(X1,sK4)
% 1.74/1.01      | ~ v1_xboole_0(X1)
% 1.74/1.01      | v1_xboole_0(X0)
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.74/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.01      | sK4 != sK4 ),
% 1.74/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_279]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_405,plain,
% 1.74/1.01      ( ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 1.74/1.01      | ~ r2_hidden(X1,sK4)
% 1.74/1.01      | ~ v1_xboole_0(X1)
% 1.74/1.01      | v1_xboole_0(X0)
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.74/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.01      | sK4 != sK4 ),
% 1.74/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_360]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_446,plain,
% 1.74/1.01      ( ~ r2_hidden(X0,sK4)
% 1.74/1.01      | ~ v1_xboole_0(X0)
% 1.74/1.01      | v1_xboole_0(X1)
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))
% 1.74/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 1.74/1.01      | sK4 != sK4 ),
% 1.74/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_405]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_491,plain,
% 1.74/1.01      ( ~ r2_hidden(X0,sK4)
% 1.74/1.01      | ~ v1_xboole_0(X0)
% 1.74/1.01      | v1_xboole_0(X1)
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))
% 1.74/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1)) ),
% 1.74/1.01      inference(equality_resolution_simp,[status(thm)],[c_446]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_568,plain,
% 1.74/1.01      ( ~ r2_hidden(X0,sK4) | ~ v1_xboole_0(X0) | ~ sP1_iProver_split ),
% 1.74/1.01      inference(splitting,
% 1.74/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.74/1.01                [c_491]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_821,plain,
% 1.74/1.01      ( r2_hidden(X0,sK4) != iProver_top
% 1.74/1.01      | v1_xboole_0(X0) != iProver_top
% 1.74/1.01      | sP1_iProver_split != iProver_top ),
% 1.74/1.01      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_2002,plain,
% 1.74/1.01      ( k3_xboole_0(k1_tarski(X0),sK4) = k1_xboole_0
% 1.74/1.01      | v1_xboole_0(X0) != iProver_top
% 1.74/1.01      | sP1_iProver_split != iProver_top ),
% 1.74/1.01      inference(superposition,[status(thm)],[c_1611,c_821]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_23,negated_conjecture,
% 1.74/1.01      ( l1_struct_0(sK3) ),
% 1.74/1.01      inference(cnf_transformation,[],[f69]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_26,plain,
% 1.74/1.01      ( l1_struct_0(sK3) = iProver_top ),
% 1.74/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_14,plain,
% 1.74/1.01      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.74/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_24,negated_conjecture,
% 1.74/1.01      ( ~ v2_struct_0(sK3) ),
% 1.74/1.01      inference(cnf_transformation,[],[f68]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_312,plain,
% 1.74/1.01      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 1.74/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_313,plain,
% 1.74/1.01      ( ~ l1_struct_0(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.74/1.01      inference(unflattening,[status(thm)],[c_312]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_314,plain,
% 1.74/1.01      ( l1_struct_0(sK3) != iProver_top
% 1.74/1.01      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 1.74/1.01      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_569,plain,
% 1.74/1.01      ( sP1_iProver_split | sP0_iProver_split ),
% 1.74/1.01      inference(splitting,
% 1.74/1.01                [splitting(split),new_symbols(definition,[])],
% 1.74/1.01                [c_491]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_598,plain,
% 1.74/1.01      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.74/1.01      inference(predicate_to_equality,[status(thm)],[c_569]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_567,plain,
% 1.74/1.01      ( v1_xboole_0(X0)
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
% 1.74/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.01      | ~ sP0_iProver_split ),
% 1.74/1.01      inference(splitting,
% 1.74/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.74/1.01                [c_491]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_822,plain,
% 1.74/1.01      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
% 1.74/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.01      | v1_xboole_0(X0) = iProver_top
% 1.74/1.01      | sP0_iProver_split != iProver_top ),
% 1.74/1.01      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_13,plain,
% 1.74/1.01      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 1.74/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_354,plain,
% 1.74/1.01      ( k2_struct_0(X0) = u1_struct_0(X0) | sK3 != X0 ),
% 1.74/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_355,plain,
% 1.74/1.01      ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 1.74/1.01      inference(unflattening,[status(thm)],[c_354]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_901,plain,
% 1.74/1.01      ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.74/1.01      | k3_lattice3(k1_lattice3(u1_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.01      | v1_xboole_0(X0) = iProver_top
% 1.74/1.01      | sP0_iProver_split != iProver_top ),
% 1.74/1.01      inference(light_normalisation,[status(thm)],[c_822,c_355]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_1004,plain,
% 1.74/1.01      ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))
% 1.74/1.01      | k3_lattice3(k1_lattice3(u1_struct_0(sK3))) != k3_lattice3(k1_lattice3(u1_struct_0(sK3)))
% 1.74/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 1.74/1.01      | sP0_iProver_split != iProver_top ),
% 1.74/1.01      inference(equality_resolution,[status(thm)],[c_901]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_1290,plain,
% 1.74/1.01      ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 1.74/1.01      | sP0_iProver_split != iProver_top ),
% 1.74/1.01      inference(equality_resolution_simp,[status(thm)],[c_1004]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_2047,plain,
% 1.74/1.01      ( v1_xboole_0(X0) != iProver_top
% 1.74/1.01      | k3_xboole_0(k1_tarski(X0),sK4) = k1_xboole_0 ),
% 1.74/1.01      inference(global_propositional_subsumption,
% 1.74/1.01                [status(thm)],
% 1.74/1.01                [c_2002,c_26,c_314,c_598,c_1290]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_2048,plain,
% 1.74/1.01      ( k3_xboole_0(k1_tarski(X0),sK4) = k1_xboole_0
% 1.74/1.01      | v1_xboole_0(X0) != iProver_top ),
% 1.74/1.01      inference(renaming,[status(thm)],[c_2047]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_2055,plain,
% 1.74/1.01      ( k3_xboole_0(k1_tarski(k1_xboole_0),sK4) = k1_xboole_0 ),
% 1.74/1.01      inference(superposition,[status(thm)],[c_830,c_2048]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_2114,plain,
% 1.74/1.01      ( k3_xboole_0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
% 1.74/1.01      inference(superposition,[status(thm)],[c_0,c_2055]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_9,plain,
% 1.74/1.01      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.74/1.01      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 1.74/1.01      inference(cnf_transformation,[],[f81]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_437,plain,
% 1.74/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X2)))
% 1.74/1.01      | sK4 != X0 ),
% 1.74/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_438,plain,
% 1.74/1.01      ( k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) = k7_subset_1(X1,sK4,X0)
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X1))) ),
% 1.74/1.01      inference(unflattening,[status(thm)],[c_437]) ).
% 1.74/1.01  
% 1.74/1.01  cnf(c_896,plain,
% 1.74/1.01      ( k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) = k7_subset_1(X1,sK4,X0)
% 1.74/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X1))) ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_438,c_355]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_976,plain,
% 1.74/1.02      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))),sK4,X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
% 1.74/1.02      inference(equality_resolution,[status(thm)],[c_896]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_15,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ l1_struct_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
% 1.74/1.02      inference(cnf_transformation,[],[f82]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_323,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))
% 1.74/1.02      | ~ l1_struct_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
% 1.74/1.02      | sK3 != X1 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_324,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 1.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 1.74/1.02      | ~ l1_struct_0(sK3)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_323]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_326,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_324,c_23]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_327,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 1.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_326]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_387,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 1.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 1.74/1.02      | sK4 != X0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_327]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_388,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 1.74/1.02      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 1.74/1.02      | v1_xboole_0(sK4)
% 1.74/1.02      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_387]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_390,plain,
% 1.74/1.02      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_388,c_22,c_20,c_18]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_877,plain,
% 1.74/1.02      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_390,c_355]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1007,plain,
% 1.74/1.02      ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) = k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) ),
% 1.74/1.02      inference(demodulation,[status(thm)],[c_976,c_877]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_17,negated_conjecture,
% 1.74/1.02      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
% 1.74/1.02      inference(cnf_transformation,[],[f75]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_852,plain,
% 1.74/1.02      ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) != sK4 ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_17,c_355]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1230,plain,
% 1.74/1.02      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) != sK4 ),
% 1.74/1.02      inference(demodulation,[status(thm)],[c_1007,c_852]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_2207,plain,
% 1.74/1.02      ( k5_xboole_0(sK4,k1_xboole_0) != sK4 ),
% 1.74/1.02      inference(demodulation,[status(thm)],[c_2114,c_1230]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_6,plain,
% 1.74/1.02      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 1.74/1.02      inference(cnf_transformation,[],[f79]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_7,plain,
% 1.74/1.02      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 1.74/1.02      inference(cnf_transformation,[],[f80]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_849,plain,
% 1.74/1.02      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_6,c_7]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_2213,plain,
% 1.74/1.02      ( sK4 != sK4 ),
% 1.74/1.02      inference(demodulation,[status(thm)],[c_2207,c_849]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_2214,plain,
% 1.74/1.02      ( $false ),
% 1.74/1.02      inference(equality_resolution_simp,[status(thm)],[c_2213]) ).
% 1.74/1.02  
% 1.74/1.02  
% 1.74/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.74/1.02  
% 1.74/1.02  ------                               Statistics
% 1.74/1.02  
% 1.74/1.02  ------ General
% 1.74/1.02  
% 1.74/1.02  abstr_ref_over_cycles:                  0
% 1.74/1.02  abstr_ref_under_cycles:                 0
% 1.74/1.02  gc_basic_clause_elim:                   0
% 1.74/1.02  forced_gc_time:                         0
% 1.74/1.02  parsing_time:                           0.008
% 1.74/1.02  unif_index_cands_time:                  0.
% 1.74/1.02  unif_index_add_time:                    0.
% 1.74/1.02  orderings_time:                         0.
% 1.74/1.02  out_proof_time:                         0.01
% 1.74/1.02  total_time:                             0.076
% 1.74/1.02  num_of_symbols:                         59
% 1.74/1.02  num_of_terms:                           1891
% 1.74/1.02  
% 1.74/1.02  ------ Preprocessing
% 1.74/1.02  
% 1.74/1.02  num_of_splits:                          2
% 1.74/1.02  num_of_split_atoms:                     2
% 1.74/1.02  num_of_reused_defs:                     0
% 1.74/1.02  num_eq_ax_congr_red:                    26
% 1.74/1.02  num_of_sem_filtered_clauses:            1
% 1.74/1.02  num_of_subtypes:                        0
% 1.74/1.02  monotx_restored_types:                  0
% 1.74/1.02  sat_num_of_epr_types:                   0
% 1.74/1.02  sat_num_of_non_cyclic_types:            0
% 1.74/1.02  sat_guarded_non_collapsed_types:        0
% 1.74/1.02  num_pure_diseq_elim:                    0
% 1.74/1.02  simp_replaced_by:                       0
% 1.74/1.02  res_preprocessed:                       112
% 1.74/1.02  prep_upred:                             0
% 1.74/1.02  prep_unflattend:                        8
% 1.74/1.02  smt_new_axioms:                         0
% 1.74/1.02  pred_elim_cands:                        2
% 1.74/1.02  pred_elim:                              7
% 1.74/1.02  pred_elim_cl:                           7
% 1.74/1.02  pred_elim_cycles:                       9
% 1.74/1.02  merged_defs:                            0
% 1.74/1.02  merged_defs_ncl:                        0
% 1.74/1.02  bin_hyper_res:                          0
% 1.74/1.02  prep_cycles:                            4
% 1.74/1.02  pred_elim_time:                         0.004
% 1.74/1.02  splitting_time:                         0.
% 1.74/1.02  sem_filter_time:                        0.
% 1.74/1.02  monotx_time:                            0.
% 1.74/1.02  subtype_inf_time:                       0.
% 1.74/1.02  
% 1.74/1.02  ------ Problem properties
% 1.74/1.02  
% 1.74/1.02  clauses:                                20
% 1.74/1.02  conjectures:                            2
% 1.74/1.02  epr:                                    5
% 1.74/1.02  horn:                                   17
% 1.74/1.02  ground:                                 7
% 1.74/1.02  unary:                                  9
% 1.74/1.02  binary:                                 7
% 1.74/1.02  lits:                                   37
% 1.74/1.02  lits_eq:                                16
% 1.74/1.02  fd_pure:                                0
% 1.74/1.02  fd_pseudo:                              0
% 1.74/1.02  fd_cond:                                3
% 1.74/1.02  fd_pseudo_cond:                         0
% 1.74/1.02  ac_symbols:                             0
% 1.74/1.02  
% 1.74/1.02  ------ Propositional Solver
% 1.74/1.02  
% 1.74/1.02  prop_solver_calls:                      28
% 1.74/1.02  prop_fast_solver_calls:                 601
% 1.74/1.02  smt_solver_calls:                       0
% 1.74/1.02  smt_fast_solver_calls:                  0
% 1.74/1.02  prop_num_of_clauses:                    743
% 1.74/1.02  prop_preprocess_simplified:             3161
% 1.74/1.02  prop_fo_subsumed:                       13
% 1.74/1.02  prop_solver_time:                       0.
% 1.74/1.02  smt_solver_time:                        0.
% 1.74/1.02  smt_fast_solver_time:                   0.
% 1.74/1.02  prop_fast_solver_time:                  0.
% 1.74/1.02  prop_unsat_core_time:                   0.
% 1.74/1.02  
% 1.74/1.02  ------ QBF
% 1.74/1.02  
% 1.74/1.02  qbf_q_res:                              0
% 1.74/1.02  qbf_num_tautologies:                    0
% 1.74/1.02  qbf_prep_cycles:                        0
% 1.74/1.02  
% 1.74/1.02  ------ BMC1
% 1.74/1.02  
% 1.74/1.02  bmc1_current_bound:                     -1
% 1.74/1.02  bmc1_last_solved_bound:                 -1
% 1.74/1.02  bmc1_unsat_core_size:                   -1
% 1.74/1.02  bmc1_unsat_core_parents_size:           -1
% 1.74/1.02  bmc1_merge_next_fun:                    0
% 1.74/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.74/1.02  
% 1.74/1.02  ------ Instantiation
% 1.74/1.02  
% 1.74/1.02  inst_num_of_clauses:                    268
% 1.74/1.02  inst_num_in_passive:                    90
% 1.74/1.02  inst_num_in_active:                     155
% 1.74/1.02  inst_num_in_unprocessed:                23
% 1.74/1.02  inst_num_of_loops:                      180
% 1.74/1.02  inst_num_of_learning_restarts:          0
% 1.74/1.02  inst_num_moves_active_passive:          21
% 1.74/1.02  inst_lit_activity:                      0
% 1.74/1.02  inst_lit_activity_moves:                0
% 1.74/1.02  inst_num_tautologies:                   0
% 1.74/1.02  inst_num_prop_implied:                  0
% 1.74/1.02  inst_num_existing_simplified:           0
% 1.74/1.02  inst_num_eq_res_simplified:             0
% 1.74/1.02  inst_num_child_elim:                    0
% 1.74/1.02  inst_num_of_dismatching_blockings:      22
% 1.74/1.02  inst_num_of_non_proper_insts:           198
% 1.74/1.02  inst_num_of_duplicates:                 0
% 1.74/1.02  inst_inst_num_from_inst_to_res:         0
% 1.74/1.02  inst_dismatching_checking_time:         0.
% 1.74/1.02  
% 1.74/1.02  ------ Resolution
% 1.74/1.02  
% 1.74/1.02  res_num_of_clauses:                     0
% 1.74/1.02  res_num_in_passive:                     0
% 1.74/1.02  res_num_in_active:                      0
% 1.74/1.02  res_num_of_loops:                       116
% 1.74/1.02  res_forward_subset_subsumed:            36
% 1.74/1.02  res_backward_subset_subsumed:           4
% 1.74/1.02  res_forward_subsumed:                   0
% 1.74/1.02  res_backward_subsumed:                  0
% 1.74/1.02  res_forward_subsumption_resolution:     0
% 1.74/1.02  res_backward_subsumption_resolution:    0
% 1.74/1.02  res_clause_to_clause_subsumption:       147
% 1.74/1.02  res_orphan_elimination:                 0
% 1.74/1.02  res_tautology_del:                      28
% 1.74/1.02  res_num_eq_res_simplified:              1
% 1.74/1.02  res_num_sel_changes:                    0
% 1.74/1.02  res_moves_from_active_to_pass:          0
% 1.74/1.02  
% 1.74/1.02  ------ Superposition
% 1.74/1.02  
% 1.74/1.02  sup_time_total:                         0.
% 1.74/1.02  sup_time_generating:                    0.
% 1.74/1.02  sup_time_sim_full:                      0.
% 1.74/1.02  sup_time_sim_immed:                     0.
% 1.74/1.02  
% 1.74/1.02  sup_num_of_clauses:                     47
% 1.74/1.02  sup_num_in_active:                      30
% 1.74/1.02  sup_num_in_passive:                     17
% 1.74/1.02  sup_num_of_loops:                       34
% 1.74/1.02  sup_fw_superposition:                   23
% 1.74/1.02  sup_bw_superposition:                   21
% 1.74/1.02  sup_immediate_simplified:               3
% 1.74/1.02  sup_given_eliminated:                   0
% 1.74/1.02  comparisons_done:                       0
% 1.74/1.02  comparisons_avoided:                    0
% 1.74/1.02  
% 1.74/1.02  ------ Simplifications
% 1.74/1.02  
% 1.74/1.02  
% 1.74/1.02  sim_fw_subset_subsumed:                 1
% 1.74/1.02  sim_bw_subset_subsumed:                 0
% 1.74/1.02  sim_fw_subsumed:                        0
% 1.74/1.02  sim_bw_subsumed:                        0
% 1.74/1.02  sim_fw_subsumption_res:                 0
% 1.74/1.02  sim_bw_subsumption_res:                 0
% 1.74/1.02  sim_tautology_del:                      1
% 1.74/1.02  sim_eq_tautology_del:                   1
% 1.74/1.02  sim_eq_res_simp:                        1
% 1.74/1.02  sim_fw_demodulated:                     2
% 1.74/1.02  sim_bw_demodulated:                     5
% 1.74/1.02  sim_light_normalised:                   6
% 1.74/1.02  sim_joinable_taut:                      0
% 1.74/1.02  sim_joinable_simp:                      0
% 1.74/1.02  sim_ac_normalised:                      0
% 1.74/1.02  sim_smt_subsumption:                    0
% 1.74/1.02  
%------------------------------------------------------------------------------
