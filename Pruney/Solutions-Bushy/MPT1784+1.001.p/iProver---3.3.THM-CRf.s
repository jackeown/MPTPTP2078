%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1784+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:24 EST 2020

% Result     : Theorem 7.30s
% Output     : CNFRefutation 7.30s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 405 expanded)
%              Number of clauses        :   83 ( 132 expanded)
%              Number of leaves         :   17 (  94 expanded)
%              Depth                    :   26
%              Number of atoms          :  482 (1535 expanded)
%              Number of equality atoms :  152 ( 180 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,sK4))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(u1_pre_topc(sK3),k5_tmap_1(sK3,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ~ r1_tarski(u1_pre_topc(sK3),k5_tmap_1(sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f48,f47])).

fof(f76,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    ~ r1_tarski(u1_pre_topc(sK3),k5_tmap_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f77,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3,X4] :
              ( r2_hidden(X4,u1_pre_topc(X1))
              & r2_hidden(X3,u1_pre_topc(X1))
              & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X5,X6] :
              ( r2_hidden(X6,u1_pre_topc(X1))
              & r2_hidden(X5,u1_pre_topc(X1))
              & k4_subset_1(u1_struct_0(X1),X5,k9_subset_1(u1_struct_0(X1),X6,X2)) = X0
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,u1_pre_topc(X1))
          & r2_hidden(X5,u1_pre_topc(X1))
          & k4_subset_1(u1_struct_0(X1),X5,k9_subset_1(u1_struct_0(X1),X6,X2)) = X0
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(sK2(X0,X1,X2),u1_pre_topc(X1))
        & r2_hidden(sK1(X0,X1,X2),u1_pre_topc(X1))
        & k4_subset_1(u1_struct_0(X1),sK1(X0,X1,X2),k9_subset_1(u1_struct_0(X1),sK2(X0,X1,X2),X2)) = X0
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),u1_pre_topc(X1))
            & r2_hidden(sK1(X0,X1,X2),u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),sK1(X0,X1,X2),k9_subset_1(u1_struct_0(X1),sK2(X0,X1,X2),X2)) = X0
            & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f44])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)),a_2_0_tmap_1(X1,X2))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1906,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_559,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_560,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_1886,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1902,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4011,plain,
    ( r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1886,c_1902])).

cnf(c_21,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1903,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4425,plain,
    ( r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4011,c_1903])).

cnf(c_7685,plain,
    ( r1_tarski(sK0(u1_pre_topc(sK3),X0),u1_struct_0(sK3)) = iProver_top
    | r1_tarski(u1_pre_topc(sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_4425])).

cnf(c_23,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_546,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_547,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_35,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_549,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_27,c_26,c_35])).

cnf(c_1887,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_7686,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_4425])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1904,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_206,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_257,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_206])).

cnf(c_1896,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_257])).

cnf(c_3579,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1904,c_1896])).

cnf(c_12831,plain,
    ( k4_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7686,c_3579])).

cnf(c_18,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_12855,plain,
    ( k4_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) = X0
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12831,c_18])).

cnf(c_14570,plain,
    ( k4_subset_1(u1_struct_0(sK3),sK0(u1_pre_topc(sK3),X0),k1_xboole_0) = sK0(u1_pre_topc(sK3),X0)
    | r1_tarski(u1_pre_topc(sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7685,c_12855])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(u1_pre_topc(sK3),k5_tmap_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1901,plain,
    ( r1_tarski(u1_pre_topc(sK3),k5_tmap_1(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_16972,plain,
    ( k4_subset_1(u1_struct_0(sK3),sK0(u1_pre_topc(sK3),k5_tmap_1(sK3,sK4)),k1_xboole_0) = sK0(u1_pre_topc(sK3),k5_tmap_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_14570,c_1901])).

cnf(c_19,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1900,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2912,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1900,c_1903])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_258,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_17,c_206])).

cnf(c_1895,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_2995,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_2912,c_1895])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X0,X3)),a_2_0_tmap_1(X1,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_468,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X0,X3)),a_2_0_tmap_1(X1,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_469,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK3))
    | ~ r2_hidden(X1,u1_pre_topc(sK3))
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k9_subset_1(u1_struct_0(sK3),X1,X2)),a_2_0_tmap_1(sK3,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_473,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK3))
    | ~ r2_hidden(X1,u1_pre_topc(sK3))
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k9_subset_1(u1_struct_0(sK3),X1,X2)),a_2_0_tmap_1(sK3,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_27,c_26])).

cnf(c_474,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK3))
    | ~ r2_hidden(X1,u1_pre_topc(sK3))
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k9_subset_1(u1_struct_0(sK3),X1,X2)),a_2_0_tmap_1(sK3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_1889,plain,
    ( r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k9_subset_1(u1_struct_0(sK3),X1,X2)),a_2_0_tmap_1(sK3,X2)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_3158,plain,
    ( r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k3_xboole_0(X1,sK4)),a_2_0_tmap_1(sK3,sK4)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2995,c_1889])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | a_2_0_tmap_1(X1,X0) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | a_2_0_tmap_1(X1,X0) = k5_tmap_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | a_2_0_tmap_1(sK3,X0) = k5_tmap_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_0_tmap_1(sK3,X0) = k5_tmap_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_27,c_26])).

cnf(c_1888,plain,
    ( a_2_0_tmap_1(sK3,X0) = k5_tmap_1(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_2182,plain,
    ( a_2_0_tmap_1(sK3,sK4) = k5_tmap_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1900,c_1888])).

cnf(c_3159,plain,
    ( r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k3_xboole_0(X1,sK4)),k5_tmap_1(sK3,sK4)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3158,c_2182])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3499,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k3_xboole_0(X1,sK4)),k5_tmap_1(sK3,sK4)) = iProver_top
    | r2_hidden(X1,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3159,c_32])).

cnf(c_3500,plain,
    ( r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k3_xboole_0(X1,sK4)),k5_tmap_1(sK3,sK4)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3499])).

cnf(c_3510,plain,
    ( r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k3_xboole_0(sK4,X1)),k5_tmap_1(sK3,sK4)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_3500])).

cnf(c_5258,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k3_xboole_0(sK4,X1)),k5_tmap_1(sK3,sK4)) = iProver_top
    | r2_hidden(X1,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3510,c_4011])).

cnf(c_5259,plain,
    ( r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k3_xboole_0(sK4,X1)),k5_tmap_1(sK3,sK4)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5258])).

cnf(c_5266,plain,
    ( r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k3_xboole_0(sK4,X1)),k5_tmap_1(sK3,sK4)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5259,c_4011])).

cnf(c_5272,plain,
    ( r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k1_xboole_0),k5_tmap_1(sK3,sK4)) = iProver_top
    | r2_hidden(k1_xboole_0,u1_pre_topc(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_5266])).

cnf(c_30,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_34,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_36,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK3)) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_5722,plain,
    ( r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k1_xboole_0),k5_tmap_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5272,c_30,c_31,c_36])).

cnf(c_5723,plain,
    ( r2_hidden(X0,u1_pre_topc(sK3)) != iProver_top
    | r2_hidden(k4_subset_1(u1_struct_0(sK3),X0,k1_xboole_0),k5_tmap_1(sK3,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5722])).

cnf(c_17115,plain,
    ( r2_hidden(sK0(u1_pre_topc(sK3),k5_tmap_1(sK3,sK4)),k5_tmap_1(sK3,sK4)) = iProver_top
    | r2_hidden(sK0(u1_pre_topc(sK3),k5_tmap_1(sK3,sK4)),u1_pre_topc(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16972,c_5723])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_813,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k5_tmap_1(sK3,sK4) != X1
    | u1_pre_topc(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_814,plain,
    ( ~ r2_hidden(sK0(u1_pre_topc(sK3),k5_tmap_1(sK3,sK4)),k5_tmap_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_815,plain,
    ( r2_hidden(sK0(u1_pre_topc(sK3),k5_tmap_1(sK3,sK4)),k5_tmap_1(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_814])).

cnf(c_806,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k5_tmap_1(sK3,sK4) != X1
    | u1_pre_topc(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_807,plain,
    ( r2_hidden(sK0(u1_pre_topc(sK3),k5_tmap_1(sK3,sK4)),u1_pre_topc(sK3)) ),
    inference(unflattening,[status(thm)],[c_806])).

cnf(c_808,plain,
    ( r2_hidden(sK0(u1_pre_topc(sK3),k5_tmap_1(sK3,sK4)),u1_pre_topc(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17115,c_815,c_808])).


%------------------------------------------------------------------------------
