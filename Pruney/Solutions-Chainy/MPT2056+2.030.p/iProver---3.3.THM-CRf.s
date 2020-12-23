%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:09 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 630 expanded)
%              Number of clauses        :   86 ( 139 expanded)
%              Number of leaves         :   21 ( 178 expanded)
%              Depth                    :   27
%              Number of atoms          :  589 (3073 expanded)
%              Number of equality atoms :  181 ( 650 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f41])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f46,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
    & ~ v1_xboole_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f45,f44])).

fof(f77,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f68,f67])).

fof(f80,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f64,f79])).

fof(f12,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f84,plain,(
    m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))))) ),
    inference(definition_unfolding,[],[f77,f80,f67])).

fof(f75,plain,(
    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f86,plain,(
    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f75,f67])).

fof(f76,plain,(
    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f76,f67])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f70,plain,(
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
    inference(definition_unfolding,[],[f70,f80,f67,f67,f67,f67])).

fof(f74,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(definition_unfolding,[],[f74,f67])).

fof(f73,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f63,f80])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f69,f67,f80,f67,f67,f67])).

fof(f78,plain,(
    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1605,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1598,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2807,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0,X1)),X0) = iProver_top
    | v1_xboole_0(k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_1598])).

cnf(c_11,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1599,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3536,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1599])).

cnf(c_3575,plain,
    ( r2_hidden(sK0(X0),k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_3536])).

cnf(c_4042,plain,
    ( v1_xboole_0(k4_xboole_0(k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2807,c_3575])).

cnf(c_4044,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4042,c_11])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1596,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15,plain,
    ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1591,plain,
    ( X0 = X1
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1592,plain,
    ( r1_xboole_0(k1_tarski(X0),X1) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2723,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1592])).

cnf(c_3076,plain,
    ( sK2(X0,k1_tarski(X1)) = X1
    | r1_xboole_0(X0,k1_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1596,c_2723])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1593,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7456,plain,
    ( sK2(X0,k1_tarski(X1)) = X1
    | k4_xboole_0(X0,k1_tarski(X1)) = X0 ),
    inference(superposition,[status(thm)],[c_3076,c_1593])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1595,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_24,negated_conjecture,
    ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_23,negated_conjecture,
    ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_20,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_25,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_369,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_370,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_372,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_26])).

cnf(c_373,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_372])).

cnf(c_458,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_373])).

cnf(c_503,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_458])).

cnf(c_544,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_503])).

cnf(c_757,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_544])).

cnf(c_1067,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_757])).

cnf(c_1587,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_2618,plain,
    ( r1_xboole_0(sK4,X0) = iProver_top
    | v1_xboole_0(sK2(sK4,X0)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1595,c_1587])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_30,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_18,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_40,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_1068,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_757])).

cnf(c_1098,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1068])).

cnf(c_1066,plain,
    ( v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_757])).

cnf(c_1588,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1066])).

cnf(c_17,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_452,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_453,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_1707,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(u1_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1588,c_453])).

cnf(c_1814,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))
    | k3_lattice3(k1_lattice3(u1_struct_0(sK3))) != k3_lattice3(k1_lattice3(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1707])).

cnf(c_2230,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1814])).

cnf(c_2833,plain,
    ( v1_xboole_0(sK2(sK4,X0)) != iProver_top
    | r1_xboole_0(sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2618,c_29,c_30,c_42,c_1098,c_2230])).

cnf(c_2834,plain,
    ( r1_xboole_0(sK4,X0) = iProver_top
    | v1_xboole_0(sK2(sK4,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2833])).

cnf(c_8506,plain,
    ( k4_xboole_0(sK4,k1_tarski(X0)) = sK4
    | r1_xboole_0(sK4,k1_tarski(X0)) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7456,c_2834])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1594,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8878,plain,
    ( r1_xboole_0(sK4,k1_tarski(X0)) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8506,c_1594])).

cnf(c_8882,plain,
    ( k4_xboole_0(sK4,k1_tarski(X0)) = sK4
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8878,c_1593])).

cnf(c_9372,plain,
    ( k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) = sK4 ),
    inference(superposition,[status(thm)],[c_4044,c_8882])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_535,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_536,plain,
    ( k7_subset_1(X0,sK4,X1) = k4_xboole_0(sK4,X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_1682,plain,
    ( k7_subset_1(X0,sK4,X1) = k4_xboole_0(sK4,X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(light_normalisation,[status(thm)],[c_536,c_453])).

cnf(c_1806,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))),sK4,X0) = k4_xboole_0(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_1682])).

cnf(c_19,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_417,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_418,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | ~ l1_struct_0(sK3)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_27])).

cnf(c_423,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(renaming,[status(thm)],[c_422])).

cnf(c_485,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_423])).

cnf(c_486,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
    | v1_xboole_0(sK4)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_488,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_26,c_24,c_22])).

cnf(c_1667,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) ),
    inference(light_normalisation,[status(thm)],[c_488,c_453])).

cnf(c_1817,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) = k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_1806,c_1667])).

cnf(c_21,negated_conjecture,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1618,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) != sK4 ),
    inference(light_normalisation,[status(thm)],[c_21,c_453])).

cnf(c_2136,plain,
    ( k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) != sK4 ),
    inference(demodulation,[status(thm)],[c_1817,c_1618])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9372,c_2136])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n003.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 19:43:57 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.31  % Running in FOF mode
% 3.41/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/0.96  
% 3.41/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.41/0.96  
% 3.41/0.96  ------  iProver source info
% 3.41/0.96  
% 3.41/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.41/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.41/0.96  git: non_committed_changes: false
% 3.41/0.96  git: last_make_outside_of_git: false
% 3.41/0.96  
% 3.41/0.96  ------ 
% 3.41/0.96  
% 3.41/0.96  ------ Input Options
% 3.41/0.96  
% 3.41/0.96  --out_options                           all
% 3.41/0.96  --tptp_safe_out                         true
% 3.41/0.96  --problem_path                          ""
% 3.41/0.96  --include_path                          ""
% 3.41/0.96  --clausifier                            res/vclausify_rel
% 3.41/0.96  --clausifier_options                    --mode clausify
% 3.41/0.96  --stdin                                 false
% 3.41/0.96  --stats_out                             all
% 3.41/0.96  
% 3.41/0.96  ------ General Options
% 3.41/0.96  
% 3.41/0.96  --fof                                   false
% 3.41/0.96  --time_out_real                         305.
% 3.41/0.96  --time_out_virtual                      -1.
% 3.41/0.96  --symbol_type_check                     false
% 3.41/0.96  --clausify_out                          false
% 3.41/0.96  --sig_cnt_out                           false
% 3.41/0.96  --trig_cnt_out                          false
% 3.41/0.96  --trig_cnt_out_tolerance                1.
% 3.41/0.96  --trig_cnt_out_sk_spl                   false
% 3.41/0.96  --abstr_cl_out                          false
% 3.41/0.96  
% 3.41/0.96  ------ Global Options
% 3.41/0.96  
% 3.41/0.96  --schedule                              default
% 3.41/0.96  --add_important_lit                     false
% 3.41/0.96  --prop_solver_per_cl                    1000
% 3.41/0.96  --min_unsat_core                        false
% 3.41/0.96  --soft_assumptions                      false
% 3.41/0.96  --soft_lemma_size                       3
% 3.41/0.96  --prop_impl_unit_size                   0
% 3.41/0.96  --prop_impl_unit                        []
% 3.41/0.96  --share_sel_clauses                     true
% 3.41/0.96  --reset_solvers                         false
% 3.41/0.96  --bc_imp_inh                            [conj_cone]
% 3.41/0.96  --conj_cone_tolerance                   3.
% 3.41/0.96  --extra_neg_conj                        none
% 3.41/0.96  --large_theory_mode                     true
% 3.41/0.96  --prolific_symb_bound                   200
% 3.41/0.96  --lt_threshold                          2000
% 3.41/0.96  --clause_weak_htbl                      true
% 3.41/0.96  --gc_record_bc_elim                     false
% 3.41/0.96  
% 3.41/0.96  ------ Preprocessing Options
% 3.41/0.96  
% 3.41/0.96  --preprocessing_flag                    true
% 3.41/0.96  --time_out_prep_mult                    0.1
% 3.41/0.96  --splitting_mode                        input
% 3.41/0.96  --splitting_grd                         true
% 3.41/0.96  --splitting_cvd                         false
% 3.41/0.96  --splitting_cvd_svl                     false
% 3.41/0.96  --splitting_nvd                         32
% 3.41/0.96  --sub_typing                            true
% 3.41/0.96  --prep_gs_sim                           true
% 3.41/0.96  --prep_unflatten                        true
% 3.41/0.96  --prep_res_sim                          true
% 3.41/0.96  --prep_upred                            true
% 3.41/0.96  --prep_sem_filter                       exhaustive
% 3.41/0.96  --prep_sem_filter_out                   false
% 3.41/0.96  --pred_elim                             true
% 3.41/0.96  --res_sim_input                         true
% 3.41/0.96  --eq_ax_congr_red                       true
% 3.41/0.96  --pure_diseq_elim                       true
% 3.41/0.96  --brand_transform                       false
% 3.41/0.96  --non_eq_to_eq                          false
% 3.41/0.96  --prep_def_merge                        true
% 3.41/0.96  --prep_def_merge_prop_impl              false
% 3.41/0.96  --prep_def_merge_mbd                    true
% 3.41/0.96  --prep_def_merge_tr_red                 false
% 3.41/0.96  --prep_def_merge_tr_cl                  false
% 3.41/0.96  --smt_preprocessing                     true
% 3.41/0.96  --smt_ac_axioms                         fast
% 3.41/0.96  --preprocessed_out                      false
% 3.41/0.96  --preprocessed_stats                    false
% 3.41/0.96  
% 3.41/0.96  ------ Abstraction refinement Options
% 3.41/0.96  
% 3.41/0.96  --abstr_ref                             []
% 3.41/0.96  --abstr_ref_prep                        false
% 3.41/0.96  --abstr_ref_until_sat                   false
% 3.41/0.96  --abstr_ref_sig_restrict                funpre
% 3.41/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/0.96  --abstr_ref_under                       []
% 3.41/0.96  
% 3.41/0.96  ------ SAT Options
% 3.41/0.96  
% 3.41/0.96  --sat_mode                              false
% 3.41/0.96  --sat_fm_restart_options                ""
% 3.41/0.96  --sat_gr_def                            false
% 3.41/0.96  --sat_epr_types                         true
% 3.41/0.96  --sat_non_cyclic_types                  false
% 3.41/0.96  --sat_finite_models                     false
% 3.41/0.96  --sat_fm_lemmas                         false
% 3.41/0.96  --sat_fm_prep                           false
% 3.41/0.96  --sat_fm_uc_incr                        true
% 3.41/0.96  --sat_out_model                         small
% 3.41/0.96  --sat_out_clauses                       false
% 3.41/0.96  
% 3.41/0.96  ------ QBF Options
% 3.41/0.96  
% 3.41/0.96  --qbf_mode                              false
% 3.41/0.96  --qbf_elim_univ                         false
% 3.41/0.96  --qbf_dom_inst                          none
% 3.41/0.96  --qbf_dom_pre_inst                      false
% 3.41/0.96  --qbf_sk_in                             false
% 3.41/0.96  --qbf_pred_elim                         true
% 3.41/0.96  --qbf_split                             512
% 3.41/0.96  
% 3.41/0.96  ------ BMC1 Options
% 3.41/0.96  
% 3.41/0.96  --bmc1_incremental                      false
% 3.41/0.96  --bmc1_axioms                           reachable_all
% 3.41/0.96  --bmc1_min_bound                        0
% 3.41/0.96  --bmc1_max_bound                        -1
% 3.41/0.96  --bmc1_max_bound_default                -1
% 3.41/0.96  --bmc1_symbol_reachability              true
% 3.41/0.96  --bmc1_property_lemmas                  false
% 3.41/0.96  --bmc1_k_induction                      false
% 3.41/0.96  --bmc1_non_equiv_states                 false
% 3.41/0.96  --bmc1_deadlock                         false
% 3.41/0.96  --bmc1_ucm                              false
% 3.41/0.96  --bmc1_add_unsat_core                   none
% 3.41/0.96  --bmc1_unsat_core_children              false
% 3.41/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/0.96  --bmc1_out_stat                         full
% 3.41/0.96  --bmc1_ground_init                      false
% 3.41/0.96  --bmc1_pre_inst_next_state              false
% 3.41/0.96  --bmc1_pre_inst_state                   false
% 3.41/0.96  --bmc1_pre_inst_reach_state             false
% 3.41/0.96  --bmc1_out_unsat_core                   false
% 3.41/0.96  --bmc1_aig_witness_out                  false
% 3.41/0.96  --bmc1_verbose                          false
% 3.41/0.96  --bmc1_dump_clauses_tptp                false
% 3.41/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.41/0.96  --bmc1_dump_file                        -
% 3.41/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.41/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.41/0.96  --bmc1_ucm_extend_mode                  1
% 3.41/0.96  --bmc1_ucm_init_mode                    2
% 3.41/0.96  --bmc1_ucm_cone_mode                    none
% 3.41/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.41/0.96  --bmc1_ucm_relax_model                  4
% 3.41/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.41/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/0.96  --bmc1_ucm_layered_model                none
% 3.41/0.96  --bmc1_ucm_max_lemma_size               10
% 3.41/0.96  
% 3.41/0.96  ------ AIG Options
% 3.41/0.96  
% 3.41/0.96  --aig_mode                              false
% 3.41/0.96  
% 3.41/0.96  ------ Instantiation Options
% 3.41/0.96  
% 3.41/0.96  --instantiation_flag                    true
% 3.41/0.96  --inst_sos_flag                         false
% 3.41/0.96  --inst_sos_phase                        true
% 3.41/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/0.96  --inst_lit_sel_side                     num_symb
% 3.41/0.96  --inst_solver_per_active                1400
% 3.41/0.96  --inst_solver_calls_frac                1.
% 3.41/0.96  --inst_passive_queue_type               priority_queues
% 3.41/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/0.96  --inst_passive_queues_freq              [25;2]
% 3.41/0.96  --inst_dismatching                      true
% 3.41/0.96  --inst_eager_unprocessed_to_passive     true
% 3.41/0.96  --inst_prop_sim_given                   true
% 3.41/0.96  --inst_prop_sim_new                     false
% 3.41/0.96  --inst_subs_new                         false
% 3.41/0.96  --inst_eq_res_simp                      false
% 3.41/0.96  --inst_subs_given                       false
% 3.41/0.96  --inst_orphan_elimination               true
% 3.41/0.96  --inst_learning_loop_flag               true
% 3.41/0.96  --inst_learning_start                   3000
% 3.41/0.96  --inst_learning_factor                  2
% 3.41/0.96  --inst_start_prop_sim_after_learn       3
% 3.41/0.96  --inst_sel_renew                        solver
% 3.41/0.96  --inst_lit_activity_flag                true
% 3.41/0.96  --inst_restr_to_given                   false
% 3.41/0.96  --inst_activity_threshold               500
% 3.41/0.96  --inst_out_proof                        true
% 3.41/0.96  
% 3.41/0.96  ------ Resolution Options
% 3.41/0.96  
% 3.41/0.96  --resolution_flag                       true
% 3.41/0.96  --res_lit_sel                           adaptive
% 3.41/0.96  --res_lit_sel_side                      none
% 3.41/0.96  --res_ordering                          kbo
% 3.41/0.96  --res_to_prop_solver                    active
% 3.41/0.96  --res_prop_simpl_new                    false
% 3.41/0.96  --res_prop_simpl_given                  true
% 3.41/0.96  --res_passive_queue_type                priority_queues
% 3.41/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/0.96  --res_passive_queues_freq               [15;5]
% 3.41/0.96  --res_forward_subs                      full
% 3.41/0.96  --res_backward_subs                     full
% 3.41/0.96  --res_forward_subs_resolution           true
% 3.41/0.96  --res_backward_subs_resolution          true
% 3.41/0.96  --res_orphan_elimination                true
% 3.41/0.96  --res_time_limit                        2.
% 3.41/0.96  --res_out_proof                         true
% 3.41/0.96  
% 3.41/0.96  ------ Superposition Options
% 3.41/0.96  
% 3.41/0.96  --superposition_flag                    true
% 3.41/0.96  --sup_passive_queue_type                priority_queues
% 3.41/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.41/0.96  --demod_completeness_check              fast
% 3.41/0.96  --demod_use_ground                      true
% 3.41/0.96  --sup_to_prop_solver                    passive
% 3.41/0.96  --sup_prop_simpl_new                    true
% 3.41/0.96  --sup_prop_simpl_given                  true
% 3.41/0.96  --sup_fun_splitting                     false
% 3.41/0.96  --sup_smt_interval                      50000
% 3.41/0.96  
% 3.41/0.96  ------ Superposition Simplification Setup
% 3.41/0.96  
% 3.41/0.96  --sup_indices_passive                   []
% 3.41/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.96  --sup_full_bw                           [BwDemod]
% 3.41/0.96  --sup_immed_triv                        [TrivRules]
% 3.41/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.96  --sup_immed_bw_main                     []
% 3.41/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.96  
% 3.41/0.96  ------ Combination Options
% 3.41/0.96  
% 3.41/0.96  --comb_res_mult                         3
% 3.41/0.96  --comb_sup_mult                         2
% 3.41/0.96  --comb_inst_mult                        10
% 3.41/0.96  
% 3.41/0.96  ------ Debug Options
% 3.41/0.96  
% 3.41/0.96  --dbg_backtrace                         false
% 3.41/0.96  --dbg_dump_prop_clauses                 false
% 3.41/0.96  --dbg_dump_prop_clauses_file            -
% 3.41/0.96  --dbg_out_stat                          false
% 3.41/0.96  ------ Parsing...
% 3.41/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.41/0.96  
% 3.41/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.41/0.96  
% 3.41/0.96  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.41/0.96  
% 3.41/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/0.96  ------ Proving...
% 3.41/0.96  ------ Problem Properties 
% 3.41/0.96  
% 3.41/0.96  
% 3.41/0.96  clauses                                 25
% 3.41/0.96  conjectures                             2
% 3.41/0.96  EPR                                     5
% 3.41/0.96  Horn                                    16
% 3.41/0.96  unary                                   6
% 3.41/0.96  binary                                  12
% 3.41/0.96  lits                                    54
% 3.41/0.96  lits eq                                 15
% 3.41/0.96  fd_pure                                 0
% 3.41/0.96  fd_pseudo                               0
% 3.41/0.96  fd_cond                                 0
% 3.41/0.96  fd_pseudo_cond                          4
% 3.41/0.96  AC symbols                              0
% 3.41/0.96  
% 3.41/0.96  ------ Schedule dynamic 5 is on 
% 3.41/0.96  
% 3.41/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.41/0.96  
% 3.41/0.96  
% 3.41/0.96  ------ 
% 3.41/0.96  Current options:
% 3.41/0.96  ------ 
% 3.41/0.96  
% 3.41/0.96  ------ Input Options
% 3.41/0.96  
% 3.41/0.96  --out_options                           all
% 3.41/0.96  --tptp_safe_out                         true
% 3.41/0.96  --problem_path                          ""
% 3.41/0.96  --include_path                          ""
% 3.41/0.96  --clausifier                            res/vclausify_rel
% 3.41/0.96  --clausifier_options                    --mode clausify
% 3.41/0.96  --stdin                                 false
% 3.41/0.96  --stats_out                             all
% 3.41/0.96  
% 3.41/0.96  ------ General Options
% 3.41/0.96  
% 3.41/0.96  --fof                                   false
% 3.41/0.96  --time_out_real                         305.
% 3.41/0.96  --time_out_virtual                      -1.
% 3.41/0.96  --symbol_type_check                     false
% 3.41/0.96  --clausify_out                          false
% 3.41/0.96  --sig_cnt_out                           false
% 3.41/0.96  --trig_cnt_out                          false
% 3.41/0.96  --trig_cnt_out_tolerance                1.
% 3.41/0.96  --trig_cnt_out_sk_spl                   false
% 3.41/0.96  --abstr_cl_out                          false
% 3.41/0.96  
% 3.41/0.96  ------ Global Options
% 3.41/0.96  
% 3.41/0.96  --schedule                              default
% 3.41/0.96  --add_important_lit                     false
% 3.41/0.96  --prop_solver_per_cl                    1000
% 3.41/0.96  --min_unsat_core                        false
% 3.41/0.96  --soft_assumptions                      false
% 3.41/0.96  --soft_lemma_size                       3
% 3.41/0.96  --prop_impl_unit_size                   0
% 3.41/0.96  --prop_impl_unit                        []
% 3.41/0.96  --share_sel_clauses                     true
% 3.41/0.96  --reset_solvers                         false
% 3.41/0.96  --bc_imp_inh                            [conj_cone]
% 3.41/0.96  --conj_cone_tolerance                   3.
% 3.41/0.96  --extra_neg_conj                        none
% 3.41/0.96  --large_theory_mode                     true
% 3.41/0.96  --prolific_symb_bound                   200
% 3.41/0.96  --lt_threshold                          2000
% 3.41/0.96  --clause_weak_htbl                      true
% 3.41/0.96  --gc_record_bc_elim                     false
% 3.41/0.96  
% 3.41/0.96  ------ Preprocessing Options
% 3.41/0.96  
% 3.41/0.96  --preprocessing_flag                    true
% 3.41/0.96  --time_out_prep_mult                    0.1
% 3.41/0.96  --splitting_mode                        input
% 3.41/0.96  --splitting_grd                         true
% 3.41/0.96  --splitting_cvd                         false
% 3.41/0.96  --splitting_cvd_svl                     false
% 3.41/0.96  --splitting_nvd                         32
% 3.41/0.96  --sub_typing                            true
% 3.41/0.96  --prep_gs_sim                           true
% 3.41/0.96  --prep_unflatten                        true
% 3.41/0.96  --prep_res_sim                          true
% 3.41/0.96  --prep_upred                            true
% 3.41/0.96  --prep_sem_filter                       exhaustive
% 3.41/0.96  --prep_sem_filter_out                   false
% 3.41/0.96  --pred_elim                             true
% 3.41/0.96  --res_sim_input                         true
% 3.41/0.96  --eq_ax_congr_red                       true
% 3.41/0.96  --pure_diseq_elim                       true
% 3.41/0.96  --brand_transform                       false
% 3.41/0.96  --non_eq_to_eq                          false
% 3.41/0.96  --prep_def_merge                        true
% 3.41/0.96  --prep_def_merge_prop_impl              false
% 3.41/0.96  --prep_def_merge_mbd                    true
% 3.41/0.96  --prep_def_merge_tr_red                 false
% 3.41/0.96  --prep_def_merge_tr_cl                  false
% 3.41/0.96  --smt_preprocessing                     true
% 3.41/0.96  --smt_ac_axioms                         fast
% 3.41/0.96  --preprocessed_out                      false
% 3.41/0.96  --preprocessed_stats                    false
% 3.41/0.96  
% 3.41/0.96  ------ Abstraction refinement Options
% 3.41/0.96  
% 3.41/0.96  --abstr_ref                             []
% 3.41/0.96  --abstr_ref_prep                        false
% 3.41/0.96  --abstr_ref_until_sat                   false
% 3.41/0.96  --abstr_ref_sig_restrict                funpre
% 3.41/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/0.96  --abstr_ref_under                       []
% 3.41/0.96  
% 3.41/0.96  ------ SAT Options
% 3.41/0.96  
% 3.41/0.96  --sat_mode                              false
% 3.41/0.96  --sat_fm_restart_options                ""
% 3.41/0.96  --sat_gr_def                            false
% 3.41/0.96  --sat_epr_types                         true
% 3.41/0.96  --sat_non_cyclic_types                  false
% 3.41/0.96  --sat_finite_models                     false
% 3.41/0.96  --sat_fm_lemmas                         false
% 3.41/0.96  --sat_fm_prep                           false
% 3.41/0.96  --sat_fm_uc_incr                        true
% 3.41/0.96  --sat_out_model                         small
% 3.41/0.96  --sat_out_clauses                       false
% 3.41/0.96  
% 3.41/0.96  ------ QBF Options
% 3.41/0.96  
% 3.41/0.96  --qbf_mode                              false
% 3.41/0.96  --qbf_elim_univ                         false
% 3.41/0.96  --qbf_dom_inst                          none
% 3.41/0.96  --qbf_dom_pre_inst                      false
% 3.41/0.96  --qbf_sk_in                             false
% 3.41/0.96  --qbf_pred_elim                         true
% 3.41/0.96  --qbf_split                             512
% 3.41/0.96  
% 3.41/0.96  ------ BMC1 Options
% 3.41/0.96  
% 3.41/0.96  --bmc1_incremental                      false
% 3.41/0.96  --bmc1_axioms                           reachable_all
% 3.41/0.96  --bmc1_min_bound                        0
% 3.41/0.96  --bmc1_max_bound                        -1
% 3.41/0.96  --bmc1_max_bound_default                -1
% 3.41/0.96  --bmc1_symbol_reachability              true
% 3.41/0.96  --bmc1_property_lemmas                  false
% 3.41/0.96  --bmc1_k_induction                      false
% 3.41/0.96  --bmc1_non_equiv_states                 false
% 3.41/0.96  --bmc1_deadlock                         false
% 3.41/0.96  --bmc1_ucm                              false
% 3.41/0.96  --bmc1_add_unsat_core                   none
% 3.41/0.96  --bmc1_unsat_core_children              false
% 3.41/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/0.96  --bmc1_out_stat                         full
% 3.41/0.96  --bmc1_ground_init                      false
% 3.41/0.96  --bmc1_pre_inst_next_state              false
% 3.41/0.96  --bmc1_pre_inst_state                   false
% 3.41/0.96  --bmc1_pre_inst_reach_state             false
% 3.41/0.96  --bmc1_out_unsat_core                   false
% 3.41/0.96  --bmc1_aig_witness_out                  false
% 3.41/0.96  --bmc1_verbose                          false
% 3.41/0.96  --bmc1_dump_clauses_tptp                false
% 3.41/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.41/0.96  --bmc1_dump_file                        -
% 3.41/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.41/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.41/0.96  --bmc1_ucm_extend_mode                  1
% 3.41/0.96  --bmc1_ucm_init_mode                    2
% 3.41/0.96  --bmc1_ucm_cone_mode                    none
% 3.41/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.41/0.96  --bmc1_ucm_relax_model                  4
% 3.41/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.41/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/0.96  --bmc1_ucm_layered_model                none
% 3.41/0.96  --bmc1_ucm_max_lemma_size               10
% 3.41/0.96  
% 3.41/0.96  ------ AIG Options
% 3.41/0.96  
% 3.41/0.96  --aig_mode                              false
% 3.41/0.96  
% 3.41/0.96  ------ Instantiation Options
% 3.41/0.96  
% 3.41/0.96  --instantiation_flag                    true
% 3.41/0.96  --inst_sos_flag                         false
% 3.41/0.96  --inst_sos_phase                        true
% 3.41/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/0.96  --inst_lit_sel_side                     none
% 3.41/0.96  --inst_solver_per_active                1400
% 3.41/0.96  --inst_solver_calls_frac                1.
% 3.41/0.96  --inst_passive_queue_type               priority_queues
% 3.41/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/0.96  --inst_passive_queues_freq              [25;2]
% 3.41/0.96  --inst_dismatching                      true
% 3.41/0.96  --inst_eager_unprocessed_to_passive     true
% 3.41/0.96  --inst_prop_sim_given                   true
% 3.41/0.96  --inst_prop_sim_new                     false
% 3.41/0.96  --inst_subs_new                         false
% 3.41/0.96  --inst_eq_res_simp                      false
% 3.41/0.96  --inst_subs_given                       false
% 3.41/0.96  --inst_orphan_elimination               true
% 3.41/0.96  --inst_learning_loop_flag               true
% 3.41/0.96  --inst_learning_start                   3000
% 3.41/0.96  --inst_learning_factor                  2
% 3.41/0.96  --inst_start_prop_sim_after_learn       3
% 3.41/0.96  --inst_sel_renew                        solver
% 3.41/0.96  --inst_lit_activity_flag                true
% 3.41/0.96  --inst_restr_to_given                   false
% 3.41/0.96  --inst_activity_threshold               500
% 3.41/0.96  --inst_out_proof                        true
% 3.41/0.96  
% 3.41/0.96  ------ Resolution Options
% 3.41/0.96  
% 3.41/0.96  --resolution_flag                       false
% 3.41/0.96  --res_lit_sel                           adaptive
% 3.41/0.96  --res_lit_sel_side                      none
% 3.41/0.96  --res_ordering                          kbo
% 3.41/0.96  --res_to_prop_solver                    active
% 3.41/0.96  --res_prop_simpl_new                    false
% 3.41/0.96  --res_prop_simpl_given                  true
% 3.41/0.96  --res_passive_queue_type                priority_queues
% 3.41/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/0.96  --res_passive_queues_freq               [15;5]
% 3.41/0.96  --res_forward_subs                      full
% 3.41/0.96  --res_backward_subs                     full
% 3.41/0.96  --res_forward_subs_resolution           true
% 3.41/0.96  --res_backward_subs_resolution          true
% 3.41/0.96  --res_orphan_elimination                true
% 3.41/0.96  --res_time_limit                        2.
% 3.41/0.96  --res_out_proof                         true
% 3.41/0.96  
% 3.41/0.96  ------ Superposition Options
% 3.41/0.96  
% 3.41/0.96  --superposition_flag                    true
% 3.41/0.96  --sup_passive_queue_type                priority_queues
% 3.41/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.41/0.96  --demod_completeness_check              fast
% 3.41/0.96  --demod_use_ground                      true
% 3.41/0.96  --sup_to_prop_solver                    passive
% 3.41/0.96  --sup_prop_simpl_new                    true
% 3.41/0.96  --sup_prop_simpl_given                  true
% 3.41/0.96  --sup_fun_splitting                     false
% 3.41/0.96  --sup_smt_interval                      50000
% 3.41/0.96  
% 3.41/0.96  ------ Superposition Simplification Setup
% 3.41/0.96  
% 3.41/0.96  --sup_indices_passive                   []
% 3.41/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.96  --sup_full_bw                           [BwDemod]
% 3.41/0.96  --sup_immed_triv                        [TrivRules]
% 3.41/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.96  --sup_immed_bw_main                     []
% 3.41/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.96  
% 3.41/0.96  ------ Combination Options
% 3.41/0.96  
% 3.41/0.96  --comb_res_mult                         3
% 3.41/0.96  --comb_sup_mult                         2
% 3.41/0.96  --comb_inst_mult                        10
% 3.41/0.96  
% 3.41/0.96  ------ Debug Options
% 3.41/0.96  
% 3.41/0.96  --dbg_backtrace                         false
% 3.41/0.96  --dbg_dump_prop_clauses                 false
% 3.41/0.96  --dbg_dump_prop_clauses_file            -
% 3.41/0.96  --dbg_out_stat                          false
% 3.41/0.96  
% 3.41/0.96  
% 3.41/0.96  
% 3.41/0.96  
% 3.41/0.96  ------ Proving...
% 3.41/0.96  
% 3.41/0.96  
% 3.41/0.96  % SZS status Theorem for theBenchmark.p
% 3.41/0.96  
% 3.41/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.41/0.96  
% 3.41/0.96  fof(f1,axiom,(
% 3.41/0.96    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f32,plain,(
% 3.41/0.96    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.41/0.96    inference(nnf_transformation,[],[f1])).
% 3.41/0.96  
% 3.41/0.96  fof(f33,plain,(
% 3.41/0.96    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.41/0.96    inference(rectify,[],[f32])).
% 3.41/0.96  
% 3.41/0.96  fof(f34,plain,(
% 3.41/0.96    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.41/0.96    introduced(choice_axiom,[])).
% 3.41/0.96  
% 3.41/0.96  fof(f35,plain,(
% 3.41/0.96    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.41/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.41/0.96  
% 3.41/0.96  fof(f48,plain,(
% 3.41/0.96    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.41/0.96    inference(cnf_transformation,[],[f35])).
% 3.41/0.96  
% 3.41/0.96  fof(f2,axiom,(
% 3.41/0.96    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f36,plain,(
% 3.41/0.96    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.41/0.96    inference(nnf_transformation,[],[f2])).
% 3.41/0.96  
% 3.41/0.96  fof(f37,plain,(
% 3.41/0.96    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.41/0.96    inference(flattening,[],[f36])).
% 3.41/0.96  
% 3.41/0.96  fof(f38,plain,(
% 3.41/0.96    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.41/0.96    inference(rectify,[],[f37])).
% 3.41/0.96  
% 3.41/0.96  fof(f39,plain,(
% 3.41/0.96    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.41/0.96    introduced(choice_axiom,[])).
% 3.41/0.96  
% 3.41/0.96  fof(f40,plain,(
% 3.41/0.96    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.41/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 3.41/0.96  
% 3.41/0.96  fof(f49,plain,(
% 3.41/0.96    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.41/0.96    inference(cnf_transformation,[],[f40])).
% 3.41/0.96  
% 3.41/0.96  fof(f90,plain,(
% 3.41/0.96    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.41/0.96    inference(equality_resolution,[],[f49])).
% 3.41/0.96  
% 3.41/0.96  fof(f4,axiom,(
% 3.41/0.96    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f58,plain,(
% 3.41/0.96    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 3.41/0.96    inference(cnf_transformation,[],[f4])).
% 3.41/0.96  
% 3.41/0.96  fof(f50,plain,(
% 3.41/0.96    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.41/0.96    inference(cnf_transformation,[],[f40])).
% 3.41/0.96  
% 3.41/0.96  fof(f89,plain,(
% 3.41/0.96    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.41/0.96    inference(equality_resolution,[],[f50])).
% 3.41/0.96  
% 3.41/0.96  fof(f3,axiom,(
% 3.41/0.96    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f18,plain,(
% 3.41/0.96    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.41/0.96    inference(rectify,[],[f3])).
% 3.41/0.96  
% 3.41/0.96  fof(f19,plain,(
% 3.41/0.96    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.41/0.96    inference(ennf_transformation,[],[f18])).
% 3.41/0.96  
% 3.41/0.96  fof(f41,plain,(
% 3.41/0.96    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.41/0.96    introduced(choice_axiom,[])).
% 3.41/0.96  
% 3.41/0.96  fof(f42,plain,(
% 3.41/0.96    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.41/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f41])).
% 3.41/0.96  
% 3.41/0.96  fof(f56,plain,(
% 3.41/0.96    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.41/0.96    inference(cnf_transformation,[],[f42])).
% 3.41/0.96  
% 3.41/0.96  fof(f7,axiom,(
% 3.41/0.96    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f21,plain,(
% 3.41/0.96    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 3.41/0.96    inference(ennf_transformation,[],[f7])).
% 3.41/0.96  
% 3.41/0.96  fof(f62,plain,(
% 3.41/0.96    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 3.41/0.96    inference(cnf_transformation,[],[f21])).
% 3.41/0.96  
% 3.41/0.96  fof(f6,axiom,(
% 3.41/0.96    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f20,plain,(
% 3.41/0.96    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.41/0.96    inference(ennf_transformation,[],[f6])).
% 3.41/0.96  
% 3.41/0.96  fof(f61,plain,(
% 3.41/0.96    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 3.41/0.96    inference(cnf_transformation,[],[f20])).
% 3.41/0.96  
% 3.41/0.96  fof(f5,axiom,(
% 3.41/0.96    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f43,plain,(
% 3.41/0.96    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.41/0.96    inference(nnf_transformation,[],[f5])).
% 3.41/0.96  
% 3.41/0.96  fof(f59,plain,(
% 3.41/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.41/0.96    inference(cnf_transformation,[],[f43])).
% 3.41/0.96  
% 3.41/0.96  fof(f55,plain,(
% 3.41/0.96    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.41/0.96    inference(cnf_transformation,[],[f42])).
% 3.41/0.96  
% 3.41/0.96  fof(f16,conjecture,(
% 3.41/0.96    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f17,negated_conjecture,(
% 3.41/0.96    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 3.41/0.96    inference(negated_conjecture,[],[f16])).
% 3.41/0.96  
% 3.41/0.96  fof(f30,plain,(
% 3.41/0.96    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 3.41/0.96    inference(ennf_transformation,[],[f17])).
% 3.41/0.96  
% 3.41/0.96  fof(f31,plain,(
% 3.41/0.96    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 3.41/0.96    inference(flattening,[],[f30])).
% 3.41/0.96  
% 3.41/0.96  fof(f45,plain,(
% 3.41/0.96    ( ! [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK4))) )),
% 3.41/0.96    introduced(choice_axiom,[])).
% 3.41/0.96  
% 3.41/0.96  fof(f44,plain,(
% 3.41/0.96    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 3.41/0.96    introduced(choice_axiom,[])).
% 3.41/0.96  
% 3.41/0.96  fof(f46,plain,(
% 3.41/0.96    (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 3.41/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f45,f44])).
% 3.41/0.96  
% 3.41/0.96  fof(f77,plain,(
% 3.41/0.96    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))),
% 3.41/0.96    inference(cnf_transformation,[],[f46])).
% 3.41/0.96  
% 3.41/0.96  fof(f9,axiom,(
% 3.41/0.96    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f64,plain,(
% 3.41/0.96    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 3.41/0.96    inference(cnf_transformation,[],[f9])).
% 3.41/0.96  
% 3.41/0.96  fof(f13,axiom,(
% 3.41/0.96    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f68,plain,(
% 3.41/0.96    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 3.41/0.96    inference(cnf_transformation,[],[f13])).
% 3.41/0.96  
% 3.41/0.96  fof(f79,plain,(
% 3.41/0.96    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 3.41/0.96    inference(definition_unfolding,[],[f68,f67])).
% 3.41/0.96  
% 3.41/0.96  fof(f80,plain,(
% 3.41/0.96    ( ! [X0] : (k1_zfmisc_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 3.41/0.96    inference(definition_unfolding,[],[f64,f79])).
% 3.41/0.96  
% 3.41/0.96  fof(f12,axiom,(
% 3.41/0.96    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f67,plain,(
% 3.41/0.96    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 3.41/0.96    inference(cnf_transformation,[],[f12])).
% 3.41/0.96  
% 3.41/0.96  fof(f84,plain,(
% 3.41/0.96    m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))),
% 3.41/0.96    inference(definition_unfolding,[],[f77,f80,f67])).
% 3.41/0.96  
% 3.41/0.96  fof(f75,plain,(
% 3.41/0.96    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 3.41/0.96    inference(cnf_transformation,[],[f46])).
% 3.41/0.96  
% 3.41/0.96  fof(f86,plain,(
% 3.41/0.96    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 3.41/0.96    inference(definition_unfolding,[],[f75,f67])).
% 3.41/0.96  
% 3.41/0.96  fof(f76,plain,(
% 3.41/0.96    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 3.41/0.96    inference(cnf_transformation,[],[f46])).
% 3.41/0.96  
% 3.41/0.96  fof(f85,plain,(
% 3.41/0.96    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 3.41/0.96    inference(definition_unfolding,[],[f76,f67])).
% 3.41/0.96  
% 3.41/0.96  fof(f15,axiom,(
% 3.41/0.96    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f28,plain,(
% 3.41/0.96    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.41/0.96    inference(ennf_transformation,[],[f15])).
% 3.41/0.96  
% 3.41/0.96  fof(f29,plain,(
% 3.41/0.96    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.41/0.96    inference(flattening,[],[f28])).
% 3.41/0.96  
% 3.41/0.96  fof(f70,plain,(
% 3.41/0.96    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.41/0.96    inference(cnf_transformation,[],[f29])).
% 3.41/0.96  
% 3.41/0.96  fof(f83,plain,(
% 3.41/0.96    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.41/0.96    inference(definition_unfolding,[],[f70,f80,f67,f67,f67,f67])).
% 3.41/0.96  
% 3.41/0.96  fof(f74,plain,(
% 3.41/0.96    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))),
% 3.41/0.96    inference(cnf_transformation,[],[f46])).
% 3.41/0.96  
% 3.41/0.96  fof(f87,plain,(
% 3.41/0.96    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))),
% 3.41/0.96    inference(definition_unfolding,[],[f74,f67])).
% 3.41/0.96  
% 3.41/0.96  fof(f73,plain,(
% 3.41/0.96    ~v1_xboole_0(sK4)),
% 3.41/0.96    inference(cnf_transformation,[],[f46])).
% 3.41/0.96  
% 3.41/0.96  fof(f71,plain,(
% 3.41/0.96    ~v2_struct_0(sK3)),
% 3.41/0.96    inference(cnf_transformation,[],[f46])).
% 3.41/0.96  
% 3.41/0.96  fof(f72,plain,(
% 3.41/0.96    l1_struct_0(sK3)),
% 3.41/0.96    inference(cnf_transformation,[],[f46])).
% 3.41/0.96  
% 3.41/0.96  fof(f11,axiom,(
% 3.41/0.96    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f24,plain,(
% 3.41/0.96    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.41/0.96    inference(ennf_transformation,[],[f11])).
% 3.41/0.96  
% 3.41/0.96  fof(f25,plain,(
% 3.41/0.96    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.41/0.96    inference(flattening,[],[f24])).
% 3.41/0.96  
% 3.41/0.96  fof(f66,plain,(
% 3.41/0.96    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.41/0.96    inference(cnf_transformation,[],[f25])).
% 3.41/0.96  
% 3.41/0.96  fof(f10,axiom,(
% 3.41/0.96    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f23,plain,(
% 3.41/0.96    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.41/0.96    inference(ennf_transformation,[],[f10])).
% 3.41/0.96  
% 3.41/0.96  fof(f65,plain,(
% 3.41/0.96    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.41/0.96    inference(cnf_transformation,[],[f23])).
% 3.41/0.96  
% 3.41/0.96  fof(f60,plain,(
% 3.41/0.96    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.41/0.96    inference(cnf_transformation,[],[f43])).
% 3.41/0.96  
% 3.41/0.96  fof(f8,axiom,(
% 3.41/0.96    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f22,plain,(
% 3.41/0.96    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.41/0.96    inference(ennf_transformation,[],[f8])).
% 3.41/0.96  
% 3.41/0.96  fof(f63,plain,(
% 3.41/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.41/0.96    inference(cnf_transformation,[],[f22])).
% 3.41/0.96  
% 3.41/0.96  fof(f81,plain,(
% 3.41/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 3.41/0.96    inference(definition_unfolding,[],[f63,f80])).
% 3.41/0.96  
% 3.41/0.96  fof(f14,axiom,(
% 3.41/0.96    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 3.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/0.96  
% 3.41/0.96  fof(f26,plain,(
% 3.41/0.96    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.41/0.96    inference(ennf_transformation,[],[f14])).
% 3.41/0.96  
% 3.41/0.96  fof(f27,plain,(
% 3.41/0.96    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.41/0.96    inference(flattening,[],[f26])).
% 3.41/0.96  
% 3.41/0.96  fof(f69,plain,(
% 3.41/0.96    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.41/0.96    inference(cnf_transformation,[],[f27])).
% 3.41/0.96  
% 3.41/0.96  fof(f82,plain,(
% 3.41/0.96    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.41/0.96    inference(definition_unfolding,[],[f69,f67,f80,f67,f67,f67])).
% 3.41/0.96  
% 3.41/0.96  fof(f78,plain,(
% 3.41/0.96    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4),
% 3.41/0.96    inference(cnf_transformation,[],[f46])).
% 3.41/0.96  
% 3.41/0.96  cnf(c_0,plain,
% 3.41/0.96      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.41/0.96      inference(cnf_transformation,[],[f48]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1605,plain,
% 3.41/0.96      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.41/0.96      | v1_xboole_0(X0) = iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_7,plain,
% 3.41/0.96      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.41/0.96      inference(cnf_transformation,[],[f90]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1598,plain,
% 3.41/0.96      ( r2_hidden(X0,X1) = iProver_top
% 3.41/0.96      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_2807,plain,
% 3.41/0.96      ( r2_hidden(sK0(k4_xboole_0(X0,X1)),X0) = iProver_top
% 3.41/0.96      | v1_xboole_0(k4_xboole_0(X0,X1)) = iProver_top ),
% 3.41/0.96      inference(superposition,[status(thm)],[c_1605,c_1598]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_11,plain,
% 3.41/0.96      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.41/0.96      inference(cnf_transformation,[],[f58]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_6,plain,
% 3.41/0.96      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.41/0.96      inference(cnf_transformation,[],[f89]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1599,plain,
% 3.41/0.96      ( r2_hidden(X0,X1) != iProver_top
% 3.41/0.96      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_3536,plain,
% 3.41/0.96      ( r2_hidden(X0,X1) != iProver_top
% 3.41/0.96      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.41/0.96      inference(superposition,[status(thm)],[c_11,c_1599]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_3575,plain,
% 3.41/0.96      ( r2_hidden(sK0(X0),k1_xboole_0) != iProver_top
% 3.41/0.96      | v1_xboole_0(X0) = iProver_top ),
% 3.41/0.96      inference(superposition,[status(thm)],[c_1605,c_3536]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_4042,plain,
% 3.41/0.96      ( v1_xboole_0(k4_xboole_0(k1_xboole_0,X0)) = iProver_top ),
% 3.41/0.96      inference(superposition,[status(thm)],[c_2807,c_3575]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_4044,plain,
% 3.41/0.96      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.41/0.96      inference(light_normalisation,[status(thm)],[c_4042,c_11]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_9,plain,
% 3.41/0.96      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1) ),
% 3.41/0.96      inference(cnf_transformation,[],[f56]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1596,plain,
% 3.41/0.96      ( r1_xboole_0(X0,X1) = iProver_top
% 3.41/0.96      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_15,plain,
% 3.41/0.96      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X1 = X0 ),
% 3.41/0.96      inference(cnf_transformation,[],[f62]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1591,plain,
% 3.41/0.96      ( X0 = X1
% 3.41/0.96      | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_14,plain,
% 3.41/0.96      ( ~ r1_xboole_0(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.41/0.96      inference(cnf_transformation,[],[f61]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1592,plain,
% 3.41/0.96      ( r1_xboole_0(k1_tarski(X0),X1) != iProver_top
% 3.41/0.96      | r2_hidden(X0,X1) != iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_2723,plain,
% 3.41/0.96      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.41/0.96      inference(superposition,[status(thm)],[c_1591,c_1592]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_3076,plain,
% 3.41/0.96      ( sK2(X0,k1_tarski(X1)) = X1
% 3.41/0.96      | r1_xboole_0(X0,k1_tarski(X1)) = iProver_top ),
% 3.41/0.96      inference(superposition,[status(thm)],[c_1596,c_2723]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_13,plain,
% 3.41/0.96      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.41/0.96      inference(cnf_transformation,[],[f59]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1593,plain,
% 3.41/0.96      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_7456,plain,
% 3.41/0.96      ( sK2(X0,k1_tarski(X1)) = X1 | k4_xboole_0(X0,k1_tarski(X1)) = X0 ),
% 3.41/0.96      inference(superposition,[status(thm)],[c_3076,c_1593]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_10,plain,
% 3.41/0.96      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0) ),
% 3.41/0.96      inference(cnf_transformation,[],[f55]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1595,plain,
% 3.41/0.96      ( r1_xboole_0(X0,X1) = iProver_top
% 3.41/0.96      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_22,negated_conjecture,
% 3.41/0.96      ( m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))))) ),
% 3.41/0.96      inference(cnf_transformation,[],[f84]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_24,negated_conjecture,
% 3.41/0.96      ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 3.41/0.96      inference(cnf_transformation,[],[f86]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_23,negated_conjecture,
% 3.41/0.96      ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 3.41/0.96      inference(cnf_transformation,[],[f85]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_20,plain,
% 3.41/0.96      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 3.41/0.96      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.41/0.96      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.41/0.96      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))
% 3.41/0.96      | ~ r2_hidden(X2,X0)
% 3.41/0.96      | ~ v1_xboole_0(X2)
% 3.41/0.96      | v1_xboole_0(X1)
% 3.41/0.96      | v1_xboole_0(X0) ),
% 3.41/0.96      inference(cnf_transformation,[],[f83]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_25,negated_conjecture,
% 3.41/0.96      ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
% 3.41/0.96      inference(cnf_transformation,[],[f87]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_369,plain,
% 3.41/0.96      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.41/0.96      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.41/0.96      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))))
% 3.41/0.96      | ~ r2_hidden(X2,X0)
% 3.41/0.96      | ~ v1_xboole_0(X2)
% 3.41/0.96      | v1_xboole_0(X0)
% 3.41/0.96      | v1_xboole_0(X1)
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 3.41/0.96      | sK4 != X0 ),
% 3.41/0.96      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_370,plain,
% 3.41/0.96      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 3.41/0.96      | ~ r2_hidden(X1,sK4)
% 3.41/0.96      | ~ v1_xboole_0(X1)
% 3.41/0.96      | v1_xboole_0(X0)
% 3.41/0.96      | v1_xboole_0(sK4)
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.41/0.96      inference(unflattening,[status(thm)],[c_369]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_26,negated_conjecture,
% 3.41/0.96      ( ~ v1_xboole_0(sK4) ),
% 3.41/0.96      inference(cnf_transformation,[],[f73]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_372,plain,
% 3.41/0.96      ( v1_xboole_0(X0)
% 3.41/0.96      | ~ v1_xboole_0(X1)
% 3.41/0.96      | ~ r2_hidden(X1,sK4)
% 3.41/0.96      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 3.41/0.96      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.41/0.96      inference(global_propositional_subsumption,
% 3.41/0.96                [status(thm)],
% 3.41/0.96                [c_370,c_26]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_373,plain,
% 3.41/0.96      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 3.41/0.96      | ~ r2_hidden(X1,sK4)
% 3.41/0.96      | ~ v1_xboole_0(X1)
% 3.41/0.96      | v1_xboole_0(X0)
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.41/0.96      inference(renaming,[status(thm)],[c_372]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_458,plain,
% 3.41/0.96      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 3.41/0.96      | ~ r2_hidden(X1,sK4)
% 3.41/0.96      | ~ v1_xboole_0(X1)
% 3.41/0.96      | v1_xboole_0(X0)
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 3.41/0.96      | sK4 != sK4 ),
% 3.41/0.96      inference(resolution_lifted,[status(thm)],[c_23,c_373]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_503,plain,
% 3.41/0.96      ( ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))))
% 3.41/0.96      | ~ r2_hidden(X1,sK4)
% 3.41/0.96      | ~ v1_xboole_0(X1)
% 3.41/0.96      | v1_xboole_0(X0)
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 3.41/0.96      | sK4 != sK4 ),
% 3.41/0.96      inference(resolution_lifted,[status(thm)],[c_24,c_458]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_544,plain,
% 3.41/0.96      ( ~ r2_hidden(X0,sK4)
% 3.41/0.96      | ~ v1_xboole_0(X0)
% 3.41/0.96      | v1_xboole_0(X1)
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))
% 3.41/0.96      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 3.41/0.96      | sK4 != sK4 ),
% 3.41/0.96      inference(resolution_lifted,[status(thm)],[c_22,c_503]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_757,plain,
% 3.41/0.96      ( ~ r2_hidden(X0,sK4)
% 3.41/0.96      | ~ v1_xboole_0(X0)
% 3.41/0.96      | v1_xboole_0(X1)
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X1))))))
% 3.41/0.96      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1)) ),
% 3.41/0.96      inference(equality_resolution_simp,[status(thm)],[c_544]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1067,plain,
% 3.41/0.96      ( ~ r2_hidden(X0,sK4) | ~ v1_xboole_0(X0) | ~ sP1_iProver_split ),
% 3.41/0.96      inference(splitting,
% 3.41/0.96                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.41/0.96                [c_757]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1587,plain,
% 3.41/0.96      ( r2_hidden(X0,sK4) != iProver_top
% 3.41/0.96      | v1_xboole_0(X0) != iProver_top
% 3.41/0.96      | sP1_iProver_split != iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_2618,plain,
% 3.41/0.96      ( r1_xboole_0(sK4,X0) = iProver_top
% 3.41/0.96      | v1_xboole_0(sK2(sK4,X0)) != iProver_top
% 3.41/0.96      | sP1_iProver_split != iProver_top ),
% 3.41/0.96      inference(superposition,[status(thm)],[c_1595,c_1587]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_28,negated_conjecture,
% 3.41/0.96      ( ~ v2_struct_0(sK3) ),
% 3.41/0.96      inference(cnf_transformation,[],[f71]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_29,plain,
% 3.41/0.96      ( v2_struct_0(sK3) != iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_27,negated_conjecture,
% 3.41/0.96      ( l1_struct_0(sK3) ),
% 3.41/0.96      inference(cnf_transformation,[],[f72]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_30,plain,
% 3.41/0.96      ( l1_struct_0(sK3) = iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_18,plain,
% 3.41/0.96      ( v2_struct_0(X0)
% 3.41/0.96      | ~ l1_struct_0(X0)
% 3.41/0.96      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.41/0.96      inference(cnf_transformation,[],[f66]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_40,plain,
% 3.41/0.96      ( v2_struct_0(X0) = iProver_top
% 3.41/0.96      | l1_struct_0(X0) != iProver_top
% 3.41/0.96      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_42,plain,
% 3.41/0.96      ( v2_struct_0(sK3) = iProver_top
% 3.41/0.96      | l1_struct_0(sK3) != iProver_top
% 3.41/0.96      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.41/0.96      inference(instantiation,[status(thm)],[c_40]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1068,plain,
% 3.41/0.96      ( sP1_iProver_split | sP0_iProver_split ),
% 3.41/0.96      inference(splitting,
% 3.41/0.96                [splitting(split),new_symbols(definition,[])],
% 3.41/0.96                [c_757]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1098,plain,
% 3.41/0.96      ( sP1_iProver_split = iProver_top
% 3.41/0.96      | sP0_iProver_split = iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_1068]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1066,plain,
% 3.41/0.96      ( v1_xboole_0(X0)
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
% 3.41/0.96      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 3.41/0.96      | ~ sP0_iProver_split ),
% 3.41/0.96      inference(splitting,
% 3.41/0.96                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.41/0.96                [c_757]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1588,plain,
% 3.41/0.96      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
% 3.41/0.96      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 3.41/0.96      | v1_xboole_0(X0) = iProver_top
% 3.41/0.96      | sP0_iProver_split != iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_1066]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_17,plain,
% 3.41/0.96      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.41/0.96      inference(cnf_transformation,[],[f65]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_452,plain,
% 3.41/0.96      ( k2_struct_0(X0) = u1_struct_0(X0) | sK3 != X0 ),
% 3.41/0.96      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_453,plain,
% 3.41/0.96      ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.41/0.96      inference(unflattening,[status(thm)],[c_452]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1707,plain,
% 3.41/0.96      ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(X0))))))
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | k3_lattice3(k1_lattice3(u1_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 3.41/0.96      | v1_xboole_0(X0) = iProver_top
% 3.41/0.96      | sP0_iProver_split != iProver_top ),
% 3.41/0.96      inference(light_normalisation,[status(thm)],[c_1588,c_453]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1814,plain,
% 3.41/0.96      ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))
% 3.41/0.96      | k3_lattice3(k1_lattice3(u1_struct_0(sK3))) != k3_lattice3(k1_lattice3(u1_struct_0(sK3)))
% 3.41/0.96      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 3.41/0.96      | sP0_iProver_split != iProver_top ),
% 3.41/0.96      inference(equality_resolution,[status(thm)],[c_1707]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_2230,plain,
% 3.41/0.96      ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 3.41/0.96      | sP0_iProver_split != iProver_top ),
% 3.41/0.96      inference(equality_resolution_simp,[status(thm)],[c_1814]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_2833,plain,
% 3.41/0.96      ( v1_xboole_0(sK2(sK4,X0)) != iProver_top
% 3.41/0.96      | r1_xboole_0(sK4,X0) = iProver_top ),
% 3.41/0.96      inference(global_propositional_subsumption,
% 3.41/0.96                [status(thm)],
% 3.41/0.96                [c_2618,c_29,c_30,c_42,c_1098,c_2230]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_2834,plain,
% 3.41/0.96      ( r1_xboole_0(sK4,X0) = iProver_top
% 3.41/0.96      | v1_xboole_0(sK2(sK4,X0)) != iProver_top ),
% 3.41/0.96      inference(renaming,[status(thm)],[c_2833]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_8506,plain,
% 3.41/0.96      ( k4_xboole_0(sK4,k1_tarski(X0)) = sK4
% 3.41/0.96      | r1_xboole_0(sK4,k1_tarski(X0)) = iProver_top
% 3.41/0.96      | v1_xboole_0(X0) != iProver_top ),
% 3.41/0.96      inference(superposition,[status(thm)],[c_7456,c_2834]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_12,plain,
% 3.41/0.96      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.41/0.96      inference(cnf_transformation,[],[f60]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1594,plain,
% 3.41/0.96      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.41/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_8878,plain,
% 3.41/0.96      ( r1_xboole_0(sK4,k1_tarski(X0)) = iProver_top
% 3.41/0.96      | v1_xboole_0(X0) != iProver_top ),
% 3.41/0.96      inference(forward_subsumption_resolution,
% 3.41/0.96                [status(thm)],
% 3.41/0.96                [c_8506,c_1594]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_8882,plain,
% 3.41/0.96      ( k4_xboole_0(sK4,k1_tarski(X0)) = sK4
% 3.41/0.96      | v1_xboole_0(X0) != iProver_top ),
% 3.41/0.96      inference(superposition,[status(thm)],[c_8878,c_1593]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_9372,plain,
% 3.41/0.96      ( k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) = sK4 ),
% 3.41/0.96      inference(superposition,[status(thm)],[c_4044,c_8882]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_16,plain,
% 3.41/0.96      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 3.41/0.96      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.41/0.96      inference(cnf_transformation,[],[f81]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_535,plain,
% 3.41/0.96      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.41/0.96      | sK4 != X1 ),
% 3.41/0.96      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_536,plain,
% 3.41/0.96      ( k7_subset_1(X0,sK4,X1) = k4_xboole_0(sK4,X1)
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.41/0.96      inference(unflattening,[status(thm)],[c_535]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1682,plain,
% 3.41/0.96      ( k7_subset_1(X0,sK4,X1) = k4_xboole_0(sK4,X1)
% 3.41/0.96      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3))))))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.41/0.96      inference(light_normalisation,[status(thm)],[c_536,c_453]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1806,plain,
% 3.41/0.96      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))),sK4,X0) = k4_xboole_0(sK4,X0) ),
% 3.41/0.96      inference(equality_resolution,[status(thm)],[c_1682]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_19,plain,
% 3.41/0.96      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 3.41/0.96      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 3.41/0.96      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))
% 3.41/0.96      | v2_struct_0(X1)
% 3.41/0.96      | ~ l1_struct_0(X1)
% 3.41/0.96      | v1_xboole_0(X0)
% 3.41/0.96      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
% 3.41/0.96      inference(cnf_transformation,[],[f82]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_417,plain,
% 3.41/0.96      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 3.41/0.96      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 3.41/0.96      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))))
% 3.41/0.96      | ~ l1_struct_0(X1)
% 3.41/0.96      | v1_xboole_0(X0)
% 3.41/0.96      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
% 3.41/0.96      | sK3 != X1 ),
% 3.41/0.96      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_418,plain,
% 3.41/0.96      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.41/0.96      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.41/0.96      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 3.41/0.96      | ~ l1_struct_0(sK3)
% 3.41/0.96      | v1_xboole_0(X0)
% 3.41/0.96      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 3.41/0.96      inference(unflattening,[status(thm)],[c_417]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_422,plain,
% 3.41/0.96      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 3.41/0.96      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.41/0.96      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.41/0.96      | v1_xboole_0(X0)
% 3.41/0.96      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 3.41/0.96      inference(global_propositional_subsumption,
% 3.41/0.96                [status(thm)],
% 3.41/0.96                [c_418,c_27]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_423,plain,
% 3.41/0.96      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.41/0.96      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.41/0.96      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 3.41/0.96      | v1_xboole_0(X0)
% 3.41/0.96      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 3.41/0.96      inference(renaming,[status(thm)],[c_422]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_485,plain,
% 3.41/0.96      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.41/0.96      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 3.41/0.96      | v1_xboole_0(X0)
% 3.41/0.96      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
% 3.41/0.96      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 3.41/0.96      | sK4 != X0 ),
% 3.41/0.96      inference(resolution_lifted,[status(thm)],[c_23,c_423]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_486,plain,
% 3.41/0.96      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.41/0.96      | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))))
% 3.41/0.96      | v1_xboole_0(sK4)
% 3.41/0.96      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 3.41/0.96      inference(unflattening,[status(thm)],[c_485]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_488,plain,
% 3.41/0.96      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 3.41/0.96      inference(global_propositional_subsumption,
% 3.41/0.96                [status(thm)],
% 3.41/0.96                [c_486,c_26,c_24,c_22]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1667,plain,
% 3.41/0.96      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) ),
% 3.41/0.96      inference(light_normalisation,[status(thm)],[c_488,c_453]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1817,plain,
% 3.41/0.96      ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) = k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) ),
% 3.41/0.96      inference(demodulation,[status(thm)],[c_1806,c_1667]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_21,negated_conjecture,
% 3.41/0.96      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
% 3.41/0.96      inference(cnf_transformation,[],[f78]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_1618,plain,
% 3.41/0.96      ( k2_yellow19(sK3,k3_yellow19(sK3,u1_struct_0(sK3),sK4)) != sK4 ),
% 3.41/0.96      inference(light_normalisation,[status(thm)],[c_21,c_453]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(c_2136,plain,
% 3.41/0.96      ( k4_xboole_0(sK4,k1_tarski(k1_xboole_0)) != sK4 ),
% 3.41/0.96      inference(demodulation,[status(thm)],[c_1817,c_1618]) ).
% 3.41/0.96  
% 3.41/0.96  cnf(contradiction,plain,
% 3.41/0.96      ( $false ),
% 3.41/0.96      inference(minisat,[status(thm)],[c_9372,c_2136]) ).
% 3.41/0.96  
% 3.41/0.96  
% 3.41/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.41/0.96  
% 3.41/0.96  ------                               Statistics
% 3.41/0.96  
% 3.41/0.96  ------ General
% 3.41/0.96  
% 3.41/0.96  abstr_ref_over_cycles:                  0
% 3.41/0.96  abstr_ref_under_cycles:                 0
% 3.41/0.96  gc_basic_clause_elim:                   0
% 3.41/0.96  forced_gc_time:                         0
% 3.41/0.96  parsing_time:                           0.013
% 3.41/0.96  unif_index_cands_time:                  0.
% 3.41/0.96  unif_index_add_time:                    0.
% 3.41/0.96  orderings_time:                         0.
% 3.41/0.96  out_proof_time:                         0.013
% 3.41/0.96  total_time:                             0.281
% 3.41/0.96  num_of_symbols:                         57
% 3.41/0.96  num_of_terms:                           8257
% 3.41/0.96  
% 3.41/0.96  ------ Preprocessing
% 3.41/0.96  
% 3.41/0.96  num_of_splits:                          2
% 3.41/0.96  num_of_split_atoms:                     2
% 3.41/0.96  num_of_reused_defs:                     0
% 3.41/0.96  num_eq_ax_congr_red:                    22
% 3.41/0.96  num_of_sem_filtered_clauses:            1
% 3.41/0.96  num_of_subtypes:                        0
% 3.41/0.96  monotx_restored_types:                  0
% 3.41/0.96  sat_num_of_epr_types:                   0
% 3.41/0.96  sat_num_of_non_cyclic_types:            0
% 3.41/0.96  sat_guarded_non_collapsed_types:        0
% 3.41/0.96  num_pure_diseq_elim:                    0
% 3.41/0.96  simp_replaced_by:                       0
% 3.41/0.96  res_preprocessed:                       131
% 3.41/0.96  prep_upred:                             0
% 3.41/0.96  prep_unflattend:                        28
% 3.41/0.96  smt_new_axioms:                         0
% 3.41/0.96  pred_elim_cands:                        3
% 3.41/0.96  pred_elim:                              6
% 3.41/0.96  pred_elim_cl:                           6
% 3.41/0.96  pred_elim_cycles:                       8
% 3.41/0.96  merged_defs:                            8
% 3.41/0.96  merged_defs_ncl:                        0
% 3.41/0.96  bin_hyper_res:                          8
% 3.41/0.96  prep_cycles:                            4
% 3.41/0.96  pred_elim_time:                         0.01
% 3.41/0.96  splitting_time:                         0.
% 3.41/0.96  sem_filter_time:                        0.
% 3.41/0.96  monotx_time:                            0.
% 3.41/0.96  subtype_inf_time:                       0.
% 3.41/0.96  
% 3.41/0.96  ------ Problem properties
% 3.41/0.96  
% 3.41/0.96  clauses:                                25
% 3.41/0.96  conjectures:                            2
% 3.41/0.96  epr:                                    5
% 3.41/0.96  horn:                                   16
% 3.41/0.96  ground:                                 6
% 3.41/0.96  unary:                                  6
% 3.41/0.96  binary:                                 12
% 3.41/0.96  lits:                                   54
% 3.41/0.96  lits_eq:                                15
% 3.41/0.96  fd_pure:                                0
% 3.41/0.96  fd_pseudo:                              0
% 3.41/0.96  fd_cond:                                0
% 3.41/0.96  fd_pseudo_cond:                         4
% 3.41/0.96  ac_symbols:                             0
% 3.41/0.96  
% 3.41/0.96  ------ Propositional Solver
% 3.41/0.96  
% 3.41/0.96  prop_solver_calls:                      27
% 3.41/0.96  prop_fast_solver_calls:                 989
% 3.41/0.96  smt_solver_calls:                       0
% 3.41/0.96  smt_fast_solver_calls:                  0
% 3.41/0.96  prop_num_of_clauses:                    3512
% 3.41/0.96  prop_preprocess_simplified:             8651
% 3.41/0.96  prop_fo_subsumed:                       25
% 3.41/0.96  prop_solver_time:                       0.
% 3.41/0.96  smt_solver_time:                        0.
% 3.41/0.96  smt_fast_solver_time:                   0.
% 3.41/0.96  prop_fast_solver_time:                  0.
% 3.41/0.96  prop_unsat_core_time:                   0.
% 3.41/0.96  
% 3.41/0.96  ------ QBF
% 3.41/0.96  
% 3.41/0.96  qbf_q_res:                              0
% 3.41/0.96  qbf_num_tautologies:                    0
% 3.41/0.96  qbf_prep_cycles:                        0
% 3.41/0.96  
% 3.41/0.96  ------ BMC1
% 3.41/0.96  
% 3.41/0.96  bmc1_current_bound:                     -1
% 3.41/0.96  bmc1_last_solved_bound:                 -1
% 3.41/0.96  bmc1_unsat_core_size:                   -1
% 3.41/0.96  bmc1_unsat_core_parents_size:           -1
% 3.41/0.96  bmc1_merge_next_fun:                    0
% 3.41/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.41/0.96  
% 3.41/0.96  ------ Instantiation
% 3.41/0.96  
% 3.41/0.96  inst_num_of_clauses:                    930
% 3.41/0.96  inst_num_in_passive:                    337
% 3.41/0.96  inst_num_in_active:                     354
% 3.41/0.96  inst_num_in_unprocessed:                239
% 3.41/0.96  inst_num_of_loops:                      480
% 3.41/0.96  inst_num_of_learning_restarts:          0
% 3.41/0.96  inst_num_moves_active_passive:          124
% 3.41/0.96  inst_lit_activity:                      0
% 3.41/0.96  inst_lit_activity_moves:                0
% 3.41/0.96  inst_num_tautologies:                   0
% 3.41/0.96  inst_num_prop_implied:                  0
% 3.41/0.96  inst_num_existing_simplified:           0
% 3.41/0.96  inst_num_eq_res_simplified:             0
% 3.41/0.96  inst_num_child_elim:                    0
% 3.41/0.96  inst_num_of_dismatching_blockings:      533
% 3.41/0.96  inst_num_of_non_proper_insts:           764
% 3.41/0.96  inst_num_of_duplicates:                 0
% 3.41/0.96  inst_inst_num_from_inst_to_res:         0
% 3.41/0.96  inst_dismatching_checking_time:         0.
% 3.41/0.96  
% 3.41/0.96  ------ Resolution
% 3.41/0.96  
% 3.41/0.96  res_num_of_clauses:                     0
% 3.41/0.96  res_num_in_passive:                     0
% 3.41/0.96  res_num_in_active:                      0
% 3.41/0.96  res_num_of_loops:                       135
% 3.41/0.96  res_forward_subset_subsumed:            45
% 3.41/0.96  res_backward_subset_subsumed:           0
% 3.41/0.96  res_forward_subsumed:                   0
% 3.41/0.96  res_backward_subsumed:                  0
% 3.41/0.96  res_forward_subsumption_resolution:     0
% 3.41/0.96  res_backward_subsumption_resolution:    0
% 3.41/0.96  res_clause_to_clause_subsumption:       1236
% 3.41/0.96  res_orphan_elimination:                 0
% 3.41/0.96  res_tautology_del:                      67
% 3.41/0.96  res_num_eq_res_simplified:              1
% 3.41/0.96  res_num_sel_changes:                    0
% 3.41/0.96  res_moves_from_active_to_pass:          0
% 3.41/0.96  
% 3.41/0.96  ------ Superposition
% 3.41/0.96  
% 3.41/0.96  sup_time_total:                         0.
% 3.41/0.96  sup_time_generating:                    0.
% 3.41/0.96  sup_time_sim_full:                      0.
% 3.41/0.96  sup_time_sim_immed:                     0.
% 3.41/0.96  
% 3.41/0.96  sup_num_of_clauses:                     204
% 3.41/0.96  sup_num_in_active:                      94
% 3.41/0.96  sup_num_in_passive:                     110
% 3.41/0.96  sup_num_of_loops:                       95
% 3.41/0.96  sup_fw_superposition:                   124
% 3.41/0.96  sup_bw_superposition:                   167
% 3.41/0.96  sup_immediate_simplified:               74
% 3.41/0.96  sup_given_eliminated:                   0
% 3.41/0.96  comparisons_done:                       0
% 3.41/0.96  comparisons_avoided:                    16
% 3.41/0.96  
% 3.41/0.96  ------ Simplifications
% 3.41/0.96  
% 3.41/0.96  
% 3.41/0.96  sim_fw_subset_subsumed:                 5
% 3.41/0.96  sim_bw_subset_subsumed:                 0
% 3.41/0.96  sim_fw_subsumed:                        46
% 3.41/0.96  sim_bw_subsumed:                        1
% 3.41/0.96  sim_fw_subsumption_res:                 3
% 3.41/0.96  sim_bw_subsumption_res:                 0
% 3.41/0.96  sim_tautology_del:                      14
% 3.41/0.96  sim_eq_tautology_del:                   6
% 3.41/0.96  sim_eq_res_simp:                        2
% 3.41/0.96  sim_fw_demodulated:                     16
% 3.41/0.96  sim_bw_demodulated:                     2
% 3.41/0.96  sim_light_normalised:                   25
% 3.41/0.96  sim_joinable_taut:                      0
% 3.41/0.96  sim_joinable_simp:                      0
% 3.41/0.96  sim_ac_normalised:                      0
% 3.41/0.96  sim_smt_subsumption:                    0
% 3.41/0.96  
%------------------------------------------------------------------------------
