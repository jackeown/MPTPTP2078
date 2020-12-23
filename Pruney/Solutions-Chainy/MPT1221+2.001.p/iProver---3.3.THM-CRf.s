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
% DateTime   : Thu Dec  3 12:13:27 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :  360 (12346259 expanded)
%              Number of clauses        :  271 (3900919 expanded)
%              Number of leaves         :   24 (2911258 expanded)
%              Depth                    :   50
%              Number of atoms          :  745 (41732267 expanded)
%              Number of equality atoms :  400 (6860222 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK3),X0)
          | ~ v4_pre_topc(sK3,X0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK3),X0)
          | v4_pre_topc(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X1),sK2)
            | ~ v4_pre_topc(X1,sK2) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X1),sK2)
            | v4_pre_topc(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
      | ~ v4_pre_topc(sK3,sK2) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
      | v4_pre_topc(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f50,f52,f51])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f81,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f72,f66])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f68,f66,f66])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f95])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f96,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f67,f66])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
    | v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1237,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1231,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_26,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_389,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_29,c_26])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_403,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_389,c_33])).

cnf(c_404,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_1252,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1231,c_404])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1239,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3992,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,X1))) = k3_subset_1(X0,k3_subset_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1239])).

cnf(c_10247,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) = k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_1252,c_3992])).

cnf(c_3994,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)) = k3_subset_1(k2_struct_0(sK2),sK3) ),
    inference(superposition,[status(thm)],[c_1252,c_1239])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4006,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) = k3_xboole_0(k2_struct_0(sK2),sK3) ),
    inference(superposition,[status(thm)],[c_3994,c_0])).

cnf(c_10251,plain,
    ( k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)) = k3_xboole_0(k2_struct_0(sK2),sK3) ),
    inference(light_normalisation,[status(thm)],[c_10247,c_4006])).

cnf(c_10385,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(k3_xboole_0(k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10251,c_1237])).

cnf(c_10554,plain,
    ( m1_subset_1(k3_xboole_0(k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_10385])).

cnf(c_17522,plain,
    ( m1_subset_1(k3_xboole_0(k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10554,c_1252])).

cnf(c_18,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1238,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1253,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1238,c_16])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1234,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2099,plain,
    ( k9_subset_1(X0,X0,k3_subset_1(X0,X1)) = k7_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1253,c_1234])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1240,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4414,plain,
    ( k9_subset_1(X0,X0,X1) = k9_subset_1(X0,X1,X0) ),
    inference(superposition,[status(thm)],[c_1253,c_1240])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1235,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2620,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1253,c_1235])).

cnf(c_4416,plain,
    ( k9_subset_1(X0,X0,X1) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_4414,c_2620])).

cnf(c_33030,plain,
    ( k3_xboole_0(k3_subset_1(X0,X1),X0) = k7_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2099,c_4416])).

cnf(c_33039,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)),k2_struct_0(sK2)) = k7_subset_1(k2_struct_0(sK2),k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_17522,c_33030])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1250,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4413,plain,
    ( k9_subset_1(k2_struct_0(sK2),sK3,X0) = k9_subset_1(k2_struct_0(sK2),X0,sK3) ),
    inference(superposition,[status(thm)],[c_1252,c_1240])).

cnf(c_2619,plain,
    ( k9_subset_1(k2_struct_0(sK2),X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_1252,c_1235])).

cnf(c_4417,plain,
    ( k9_subset_1(k2_struct_0(sK2),sK3,X0) = k3_xboole_0(X0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_4413,c_2619])).

cnf(c_2098,plain,
    ( k9_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),X0)) = k7_subset_1(k2_struct_0(sK2),sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1252,c_1234])).

cnf(c_3869,plain,
    ( k9_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),X0))) = k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_2098])).

cnf(c_4214,plain,
    ( k9_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) = k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_1252,c_3869])).

cnf(c_4598,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),sK3) = k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_4417,c_4214])).

cnf(c_14,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1641,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_14,c_24])).

cnf(c_1781,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1641,c_24])).

cnf(c_4691,plain,
    ( k3_xboole_0(sK3,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) = k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_4598,c_1781])).

cnf(c_1785,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1781,c_0])).

cnf(c_2236,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1785,c_0])).

cnf(c_1645,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_0])).

cnf(c_2847,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_2236,c_1645])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1245,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7930,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2847,c_1245])).

cnf(c_7948,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7930,c_0])).

cnf(c_8604,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) = iProver_top
    | r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4691,c_7948])).

cnf(c_8611,plain,
    ( r2_hidden(X0,k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3))) = iProver_top
    | r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8604,c_4598])).

cnf(c_10375,plain,
    ( k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)) = k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)) ),
    inference(demodulation,[status(thm)],[c_10251,c_4691])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1246,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1236,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3711,plain,
    ( r2_hidden(X0,k2_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1252,c_1236])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1247,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8878,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k2_struct_0(sK2))) = X1
    | r2_hidden(sK1(X0,k2_struct_0(sK2),X1),X1) = iProver_top
    | r2_hidden(sK1(X0,k2_struct_0(sK2),X1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3711,c_1247])).

cnf(c_8966,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2))) = X0
    | r2_hidden(sK1(sK3,k2_struct_0(sK2),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_8878])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1243,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4684,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) = iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4598,c_1243])).

cnf(c_11739,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4684,c_10251,c_10375])).

cnf(c_7920,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) = iProver_top
    | r2_hidden(X0,k2_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3994,c_1245])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1244,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4481,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4006,c_1244])).

cnf(c_8395,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7920,c_4481])).

cnf(c_4133,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4006,c_1243])).

cnf(c_9147,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8395,c_4133])).

cnf(c_4685,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4598,c_1244])).

cnf(c_10373,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10251,c_4685])).

cnf(c_10380,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10373,c_10375])).

cnf(c_11743,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11739,c_9147,c_10380])).

cnf(c_12700,plain,
    ( k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))) = k5_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2))) ),
    inference(superposition,[status(thm)],[c_8966,c_11743])).

cnf(c_2330,plain,
    ( k9_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)) = k7_subset_1(k2_struct_0(sK2),sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1252,c_2098])).

cnf(c_4594,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),sK3) = k7_subset_1(k2_struct_0(sK2),sK3,sK3) ),
    inference(superposition,[status(thm)],[c_4417,c_2330])).

cnf(c_4605,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),sK3))) = k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_4594,c_1645])).

cnf(c_4622,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3))) ),
    inference(demodulation,[status(thm)],[c_4605,c_4594])).

cnf(c_4615,plain,
    ( k3_xboole_0(sK3,k3_subset_1(k2_struct_0(sK2),sK3)) = k7_subset_1(k2_struct_0(sK2),sK3,sK3) ),
    inference(superposition,[status(thm)],[c_4594,c_1781])).

cnf(c_4486,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2847,c_1244])).

cnf(c_4491,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4486,c_0])).

cnf(c_6816,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4615,c_4491])).

cnf(c_6819,plain,
    ( r2_hidden(X0,k7_subset_1(k2_struct_0(sK2),sK3,sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6816,c_4594])).

cnf(c_4480,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3994,c_1244])).

cnf(c_7935,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3))) = iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4594,c_1245])).

cnf(c_4607,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3)))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),sK3) ),
    inference(superposition,[status(thm)],[c_4594,c_0])).

cnf(c_4621,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3)))) = k7_subset_1(k2_struct_0(sK2),sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_4607,c_4594])).

cnf(c_9258,plain,
    ( r2_hidden(X0,k7_subset_1(k2_struct_0(sK2),sK3,sK3)) != iProver_top
    | r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4621,c_1243])).

cnf(c_9265,plain,
    ( r2_hidden(X0,k7_subset_1(k2_struct_0(sK2),sK3,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6819,c_4480,c_7935,c_9258])).

cnf(c_9271,plain,
    ( r1_tarski(k7_subset_1(k2_struct_0(sK2),sK3,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_9265])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1786,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1781,c_13])).

cnf(c_1871,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1786,c_0])).

cnf(c_1872,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1871,c_1786])).

cnf(c_4487,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_1244])).

cnf(c_1874,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1872,c_13])).

cnf(c_4490,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4487,c_1874])).

cnf(c_9528,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_4490])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1242,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9541,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9528,c_1242])).

cnf(c_10346,plain,
    ( k7_subset_1(k2_struct_0(sK2),sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9271,c_9541])).

cnf(c_10921,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_4622,c_4622,c_10346])).

cnf(c_10922,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) = k3_subset_1(k2_struct_0(sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_10921,c_13])).

cnf(c_10927,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)))) = k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) ),
    inference(superposition,[status(thm)],[c_10922,c_1645])).

cnf(c_10948,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) ),
    inference(demodulation,[status(thm)],[c_10927,c_10922])).

cnf(c_3868,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k3_xboole_0(X1,k3_subset_1(X0,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1235])).

cnf(c_9457,plain,
    ( k9_subset_1(k2_struct_0(sK2),X0,k3_subset_1(k2_struct_0(sK2),sK3)) = k3_xboole_0(X0,k3_subset_1(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_1252,c_3868])).

cnf(c_3866,plain,
    ( k9_subset_1(X0,k3_subset_1(X0,X1),k3_subset_1(X0,X2)) = k7_subset_1(X0,k3_subset_1(X0,X1),X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1234])).

cnf(c_7311,plain,
    ( k9_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),X0)) = k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1252,c_3866])).

cnf(c_8173,plain,
    ( k9_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)) = k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3) ),
    inference(superposition,[status(thm)],[c_1252,c_7311])).

cnf(c_9803,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)) = k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3) ),
    inference(superposition,[status(thm)],[c_9457,c_8173])).

cnf(c_1644,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_9827,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3)) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9803,c_1644])).

cnf(c_10949,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_10948,c_9803,c_9827])).

cnf(c_10983,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10949,c_1244])).

cnf(c_10997,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10983,c_13])).

cnf(c_10930,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) = iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10922,c_1243])).

cnf(c_11142,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10997,c_10930])).

cnf(c_12701,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)) = k5_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2))) ),
    inference(superposition,[status(thm)],[c_8966,c_11142])).

cnf(c_10926,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0),k3_subset_1(k2_struct_0(sK2),sK3)))) = k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) ),
    inference(superposition,[status(thm)],[c_10922,c_2236])).

cnf(c_10951,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0),k3_subset_1(k2_struct_0(sK2),sK3)))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_10926,c_9803,c_9827])).

cnf(c_9814,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9803,c_4491])).

cnf(c_9836,plain,
    ( r2_hidden(X0,k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9814,c_9803,c_9827])).

cnf(c_9815,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9803,c_1244])).

cnf(c_9835,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9815,c_9827])).

cnf(c_9812,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) = iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9803,c_1243])).

cnf(c_9838,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) = iProver_top
    | r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9812,c_9827])).

cnf(c_10010,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9836,c_9835,c_9838])).

cnf(c_10016,plain,
    ( r1_tarski(k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_10010])).

cnf(c_11228,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10016,c_9541])).

cnf(c_11364,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0),k3_subset_1(k2_struct_0(sK2),sK3)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10951,c_10951,c_11228])).

cnf(c_11373,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0),k3_subset_1(k2_struct_0(sK2),sK3)))) = k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_11364,c_0])).

cnf(c_2001,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1644,c_0])).

cnf(c_2107,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1781,c_2001])).

cnf(c_2531,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2107,c_0])).

cnf(c_9825,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k1_xboole_0,k3_subset_1(k2_struct_0(sK2),sK3))) ),
    inference(superposition,[status(thm)],[c_9803,c_2531])).

cnf(c_2110,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) = k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2001,c_0])).

cnf(c_9826,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_9803,c_2110])).

cnf(c_9828,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k1_xboole_0,k3_subset_1(k2_struct_0(sK2),sK3))) ),
    inference(demodulation,[status(thm)],[c_9825,c_9826])).

cnf(c_11389,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) = k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11364,c_1785])).

cnf(c_11390,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0) = k3_subset_1(k2_struct_0(sK2),sK3) ),
    inference(light_normalisation,[status(thm)],[c_11389,c_10922])).

cnf(c_11559,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k1_xboole_0,k3_subset_1(k2_struct_0(sK2),sK3))) = k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)) ),
    inference(light_normalisation,[status(thm)],[c_11373,c_9803,c_9827,c_9828,c_10922,c_11390])).

cnf(c_11391,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11390,c_11364])).

cnf(c_11392,plain,
    ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k1_xboole_0,k3_subset_1(k2_struct_0(sK2),sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11391,c_9803,c_9827,c_9828])).

cnf(c_11560,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11559,c_11392])).

cnf(c_12702,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12701,c_11560])).

cnf(c_12714,plain,
    ( k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12700,c_12702])).

cnf(c_15698,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8611,c_10251,c_10375,c_12714])).

cnf(c_15702,plain,
    ( r2_hidden(X0,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))) = iProver_top
    | r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15698,c_4490])).

cnf(c_15703,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_15702])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1251,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15711,plain,
    ( r2_hidden(sK0(X0,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))),k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
    | r1_tarski(X0,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15703,c_1251])).

cnf(c_2677,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1781,c_1645])).

cnf(c_4689,plain,
    ( k3_xboole_0(sK3,k5_xboole_0(sK3,k3_xboole_0(sK3,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))))) = k5_xboole_0(sK3,k3_xboole_0(sK3,k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) ),
    inference(superposition,[status(thm)],[c_4598,c_2677])).

cnf(c_4693,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) = k3_xboole_0(sK3,k5_xboole_0(sK3,k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) ),
    inference(demodulation,[status(thm)],[c_4689,c_4691])).

cnf(c_18534,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)))) = k3_xboole_0(sK3,k5_xboole_0(sK3,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)))) ),
    inference(light_normalisation,[status(thm)],[c_4693,c_4693,c_10375])).

cnf(c_2843,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1781,c_2236])).

cnf(c_3380,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2677,c_0])).

cnf(c_6302,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_3380,c_0])).

cnf(c_8875,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
    | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_1247])).

cnf(c_8881,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = X1
    | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8875,c_1644])).

cnf(c_14890,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8881,c_11142])).

cnf(c_14891,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14890,c_11560])).

cnf(c_18535,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18534,c_2843,c_6302,c_12702,c_14891])).

cnf(c_3597,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2843,c_0])).

cnf(c_18563,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)) = k5_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18535,c_3597])).

cnf(c_2323,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k3_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_2110,c_0])).

cnf(c_2860,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0))) = k3_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_2323,c_2236])).

cnf(c_16016,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_2860,c_1786,c_2860,c_14891])).

cnf(c_2611,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)))) = k3_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_2531,c_0])).

cnf(c_16020,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)))) = k3_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_16016,c_2611])).

cnf(c_16022,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_16016,c_2531])).

cnf(c_16025,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_16022,c_1644,c_14891])).

cnf(c_16027,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_16020,c_16025])).

cnf(c_16028,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_16027,c_13])).

cnf(c_16021,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k3_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_16016,c_2323])).

cnf(c_16026,plain,
    ( k3_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_16021,c_14891])).

cnf(c_16029,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_16028,c_16026])).

cnf(c_17536,plain,
    ( k9_subset_1(k2_struct_0(sK2),X0,k3_xboole_0(k2_struct_0(sK2),sK3)) = k3_xboole_0(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_17522,c_1235])).

cnf(c_17814,plain,
    ( k9_subset_1(k2_struct_0(sK2),X0,k3_xboole_0(sK3,k2_struct_0(sK2))) = k3_xboole_0(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_1781,c_17536])).

cnf(c_17526,plain,
    ( m1_subset_1(k3_xboole_0(sK3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_17522])).

cnf(c_17790,plain,
    ( k9_subset_1(k2_struct_0(sK2),X0,k3_xboole_0(sK3,k2_struct_0(sK2))) = k3_xboole_0(X0,k3_xboole_0(sK3,k2_struct_0(sK2))) ),
    inference(superposition,[status(thm)],[c_17526,c_1235])).

cnf(c_17817,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK3,k2_struct_0(sK2))) = k3_xboole_0(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) ),
    inference(light_normalisation,[status(thm)],[c_17814,c_17790])).

cnf(c_18566,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_18563,c_16029,c_17817])).

cnf(c_22547,plain,
    ( r2_hidden(sK0(X0,sK3),k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15711,c_18566])).

cnf(c_22551,plain,
    ( r1_tarski(k3_xboole_0(k2_struct_0(sK2),sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_22547])).

cnf(c_7921,plain,
    ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) = iProver_top
    | r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) = iProver_top
    | r2_hidden(X0,k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4006,c_1245])).

cnf(c_13270,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) = iProver_top
    | r2_hidden(X0,k2_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7921,c_4480])).

cnf(c_13289,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13270,c_3711])).

cnf(c_13297,plain,
    ( r2_hidden(sK0(X0,k3_xboole_0(k2_struct_0(sK2),sK3)),sK3) != iProver_top
    | r1_tarski(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13289,c_1251])).

cnf(c_18527,plain,
    ( r1_tarski(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_13297])).

cnf(c_18747,plain,
    ( k3_xboole_0(k2_struct_0(sK2),sK3) = sK3
    | r1_tarski(k3_xboole_0(k2_struct_0(sK2),sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_18527,c_1242])).

cnf(c_23250,plain,
    ( k3_xboole_0(k2_struct_0(sK2),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_22551,c_18747])).

cnf(c_4683,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3))))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),sK3) ),
    inference(superposition,[status(thm)],[c_4598,c_0])).

cnf(c_4697,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3))))) = k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)) ),
    inference(demodulation,[status(thm)],[c_4683,c_4598])).

cnf(c_11971,plain,
    ( k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))))) = k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)) ),
    inference(light_normalisation,[status(thm)],[c_4697,c_4697,c_10251,c_10375])).

cnf(c_11980,plain,
    ( k5_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k3_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k5_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k3_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2)))))) = k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_1781,c_11971])).

cnf(c_14867,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X0
    | k3_xboole_0(X0,k1_xboole_0) = X0
    | r2_hidden(sK1(X0,X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8881,c_1247])).

cnf(c_15064,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0,X0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14867,c_1644,c_14891])).

cnf(c_11756,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k3_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_11743])).

cnf(c_17095,plain,
    ( k5_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k3_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15064,c_11756])).

cnf(c_23524,plain,
    ( k5_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k3_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k1_xboole_0)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_11980,c_11980,c_17095,c_18566])).

cnf(c_23525,plain,
    ( k3_xboole_0(sK3,k2_struct_0(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_23524,c_13,c_14891,c_16029])).

cnf(c_4003,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(sK3,k2_struct_0(sK2))) = k3_subset_1(k2_struct_0(sK2),sK3) ),
    inference(superposition,[status(thm)],[c_1781,c_3994])).

cnf(c_23555,plain,
    ( k3_subset_1(k2_struct_0(sK2),sK3) = k5_xboole_0(k2_struct_0(sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_23525,c_4003])).

cnf(c_23818,plain,
    ( m1_subset_1(k5_xboole_0(k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_23555,c_1237])).

cnf(c_25430,plain,
    ( m1_subset_1(k5_xboole_0(k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23818,c_1252])).

cnf(c_25437,plain,
    ( k9_subset_1(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3),X0) = k9_subset_1(k2_struct_0(sK2),X0,k5_xboole_0(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_25430,c_1240])).

cnf(c_23706,plain,
    ( k9_subset_1(k2_struct_0(sK2),X0,k5_xboole_0(k2_struct_0(sK2),sK3)) = k3_xboole_0(X0,k5_xboole_0(k2_struct_0(sK2),sK3)) ),
    inference(demodulation,[status(thm)],[c_23555,c_9457])).

cnf(c_25456,plain,
    ( k9_subset_1(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3),X0) = k3_xboole_0(X0,k5_xboole_0(k2_struct_0(sK2),sK3)) ),
    inference(light_normalisation,[status(thm)],[c_25437,c_23706])).

cnf(c_25538,plain,
    ( k3_xboole_0(k5_xboole_0(k2_struct_0(sK2),sK3),k2_struct_0(sK2)) = k3_xboole_0(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_25456,c_2620])).

cnf(c_6284,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(sK3,k2_struct_0(sK2))) ),
    inference(superposition,[status(thm)],[c_3994,c_3380])).

cnf(c_2680,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1645,c_0])).

cnf(c_6918,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(sK3,k2_struct_0(sK2)))))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)))) ),
    inference(superposition,[status(thm)],[c_6284,c_2680])).

cnf(c_23550,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)))) ),
    inference(demodulation,[status(thm)],[c_23525,c_6918])).

cnf(c_6919,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(sK3,k2_struct_0(sK2))))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) ),
    inference(superposition,[status(thm)],[c_6284,c_0])).

cnf(c_23552,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) ),
    inference(demodulation,[status(thm)],[c_23525,c_6919])).

cnf(c_23560,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3))) ),
    inference(demodulation,[status(thm)],[c_23552,c_23555])).

cnf(c_4132,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3))) = k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_4006,c_0])).

cnf(c_23561,plain,
    ( k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3))) = k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)) ),
    inference(light_normalisation,[status(thm)],[c_23560,c_4132])).

cnf(c_23564,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) ),
    inference(demodulation,[status(thm)],[c_23550,c_23555,c_23561])).

cnf(c_23565,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)))) = k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)) ),
    inference(demodulation,[status(thm)],[c_23564,c_23555,c_23561])).

cnf(c_23566,plain,
    ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)))) = k3_xboole_0(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3)) ),
    inference(demodulation,[status(thm)],[c_23565,c_23555])).

cnf(c_23567,plain,
    ( k3_xboole_0(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3)) = k5_xboole_0(k2_struct_0(sK2),sK3) ),
    inference(light_normalisation,[status(thm)],[c_23566,c_23250])).

cnf(c_25540,plain,
    ( k3_xboole_0(k5_xboole_0(k2_struct_0(sK2),sK3),k2_struct_0(sK2)) = k5_xboole_0(k2_struct_0(sK2),sK3) ),
    inference(light_normalisation,[status(thm)],[c_25538,c_23567])).

cnf(c_33042,plain,
    ( k7_subset_1(k2_struct_0(sK2),k2_struct_0(sK2),sK3) = k5_xboole_0(k2_struct_0(sK2),sK3) ),
    inference(light_normalisation,[status(thm)],[c_33039,c_23250,c_23555,c_25540])).

cnf(c_30,negated_conjecture,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_229,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_230,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_27,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_423,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_424,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0),sK2)
    | v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_463,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0),sK2)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_424])).

cnf(c_464,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_562,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) ),
    inference(prop_impl,[status(thm)],[c_32,c_464])).

cnf(c_563,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) ),
    inference(renaming,[status(thm)],[c_562])).

cnf(c_1229,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_1255,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) != iProver_top
    | v3_pre_topc(k3_subset_1(k2_struct_0(sK2),sK3),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1229,c_404])).

cnf(c_23728,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) != iProver_top
    | v3_pre_topc(k5_xboole_0(k2_struct_0(sK2),sK3),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23555,c_1255])).

cnf(c_33084,plain,
    ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK2),sK3),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33042,c_23728])).

cnf(c_31,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
    | v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_231,plain,
    ( v4_pre_topc(sK3,sK2)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_232,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
    | v4_pre_topc(sK3,sK2) ),
    inference(renaming,[status(thm)],[c_231])).

cnf(c_28,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_408,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_33])).

cnf(c_409,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0),sK2)
    | ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_449,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0),sK2)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_232,c_409])).

cnf(c_450,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_564,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) ),
    inference(prop_impl,[status(thm)],[c_32,c_450])).

cnf(c_565,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) ),
    inference(renaming,[status(thm)],[c_564])).

cnf(c_1230,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) = iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_1254,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) = iProver_top
    | v3_pre_topc(k3_subset_1(k2_struct_0(sK2),sK3),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1230,c_404])).

cnf(c_23727,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) = iProver_top
    | v3_pre_topc(k5_xboole_0(k2_struct_0(sK2),sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23555,c_1254])).

cnf(c_33083,plain,
    ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK2),sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_33042,c_23727])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33084,c_33083])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:13:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.08/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.08/1.50  
% 8.08/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.08/1.50  
% 8.08/1.50  ------  iProver source info
% 8.08/1.50  
% 8.08/1.50  git: date: 2020-06-30 10:37:57 +0100
% 8.08/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.08/1.50  git: non_committed_changes: false
% 8.08/1.50  git: last_make_outside_of_git: false
% 8.08/1.50  
% 8.08/1.50  ------ 
% 8.08/1.50  
% 8.08/1.50  ------ Input Options
% 8.08/1.50  
% 8.08/1.50  --out_options                           all
% 8.08/1.50  --tptp_safe_out                         true
% 8.08/1.50  --problem_path                          ""
% 8.08/1.50  --include_path                          ""
% 8.08/1.50  --clausifier                            res/vclausify_rel
% 8.08/1.50  --clausifier_options                    ""
% 8.08/1.50  --stdin                                 false
% 8.08/1.50  --stats_out                             all
% 8.08/1.50  
% 8.08/1.50  ------ General Options
% 8.08/1.50  
% 8.08/1.50  --fof                                   false
% 8.08/1.50  --time_out_real                         305.
% 8.08/1.50  --time_out_virtual                      -1.
% 8.08/1.50  --symbol_type_check                     false
% 8.08/1.50  --clausify_out                          false
% 8.08/1.50  --sig_cnt_out                           false
% 8.08/1.50  --trig_cnt_out                          false
% 8.08/1.50  --trig_cnt_out_tolerance                1.
% 8.08/1.50  --trig_cnt_out_sk_spl                   false
% 8.08/1.50  --abstr_cl_out                          false
% 8.08/1.50  
% 8.08/1.50  ------ Global Options
% 8.08/1.50  
% 8.08/1.50  --schedule                              default
% 8.08/1.50  --add_important_lit                     false
% 8.08/1.50  --prop_solver_per_cl                    1000
% 8.08/1.50  --min_unsat_core                        false
% 8.08/1.50  --soft_assumptions                      false
% 8.08/1.50  --soft_lemma_size                       3
% 8.08/1.50  --prop_impl_unit_size                   0
% 8.08/1.50  --prop_impl_unit                        []
% 8.08/1.50  --share_sel_clauses                     true
% 8.08/1.50  --reset_solvers                         false
% 8.08/1.50  --bc_imp_inh                            [conj_cone]
% 8.08/1.50  --conj_cone_tolerance                   3.
% 8.08/1.50  --extra_neg_conj                        none
% 8.08/1.50  --large_theory_mode                     true
% 8.08/1.50  --prolific_symb_bound                   200
% 8.08/1.50  --lt_threshold                          2000
% 8.08/1.50  --clause_weak_htbl                      true
% 8.08/1.50  --gc_record_bc_elim                     false
% 8.08/1.50  
% 8.08/1.50  ------ Preprocessing Options
% 8.08/1.50  
% 8.08/1.50  --preprocessing_flag                    true
% 8.08/1.50  --time_out_prep_mult                    0.1
% 8.08/1.50  --splitting_mode                        input
% 8.08/1.50  --splitting_grd                         true
% 8.08/1.50  --splitting_cvd                         false
% 8.08/1.50  --splitting_cvd_svl                     false
% 8.08/1.50  --splitting_nvd                         32
% 8.08/1.50  --sub_typing                            true
% 8.08/1.50  --prep_gs_sim                           true
% 8.08/1.50  --prep_unflatten                        true
% 8.08/1.50  --prep_res_sim                          true
% 8.08/1.50  --prep_upred                            true
% 8.08/1.50  --prep_sem_filter                       exhaustive
% 8.08/1.50  --prep_sem_filter_out                   false
% 8.08/1.50  --pred_elim                             true
% 8.08/1.50  --res_sim_input                         true
% 8.08/1.50  --eq_ax_congr_red                       true
% 8.08/1.50  --pure_diseq_elim                       true
% 8.08/1.50  --brand_transform                       false
% 8.08/1.50  --non_eq_to_eq                          false
% 8.08/1.50  --prep_def_merge                        true
% 8.08/1.50  --prep_def_merge_prop_impl              false
% 8.08/1.50  --prep_def_merge_mbd                    true
% 8.08/1.50  --prep_def_merge_tr_red                 false
% 8.08/1.50  --prep_def_merge_tr_cl                  false
% 8.08/1.50  --smt_preprocessing                     true
% 8.08/1.50  --smt_ac_axioms                         fast
% 8.08/1.50  --preprocessed_out                      false
% 8.08/1.50  --preprocessed_stats                    false
% 8.08/1.50  
% 8.08/1.50  ------ Abstraction refinement Options
% 8.08/1.50  
% 8.08/1.50  --abstr_ref                             []
% 8.08/1.50  --abstr_ref_prep                        false
% 8.08/1.50  --abstr_ref_until_sat                   false
% 8.08/1.50  --abstr_ref_sig_restrict                funpre
% 8.08/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.08/1.50  --abstr_ref_under                       []
% 8.08/1.50  
% 8.08/1.50  ------ SAT Options
% 8.08/1.50  
% 8.08/1.50  --sat_mode                              false
% 8.08/1.50  --sat_fm_restart_options                ""
% 8.08/1.50  --sat_gr_def                            false
% 8.08/1.50  --sat_epr_types                         true
% 8.08/1.50  --sat_non_cyclic_types                  false
% 8.08/1.50  --sat_finite_models                     false
% 8.08/1.50  --sat_fm_lemmas                         false
% 8.08/1.50  --sat_fm_prep                           false
% 8.08/1.50  --sat_fm_uc_incr                        true
% 8.08/1.50  --sat_out_model                         small
% 8.08/1.50  --sat_out_clauses                       false
% 8.08/1.50  
% 8.08/1.50  ------ QBF Options
% 8.08/1.50  
% 8.08/1.50  --qbf_mode                              false
% 8.08/1.50  --qbf_elim_univ                         false
% 8.08/1.50  --qbf_dom_inst                          none
% 8.08/1.50  --qbf_dom_pre_inst                      false
% 8.08/1.50  --qbf_sk_in                             false
% 8.08/1.50  --qbf_pred_elim                         true
% 8.08/1.50  --qbf_split                             512
% 8.08/1.50  
% 8.08/1.50  ------ BMC1 Options
% 8.08/1.50  
% 8.08/1.50  --bmc1_incremental                      false
% 8.08/1.50  --bmc1_axioms                           reachable_all
% 8.08/1.50  --bmc1_min_bound                        0
% 8.08/1.50  --bmc1_max_bound                        -1
% 8.08/1.50  --bmc1_max_bound_default                -1
% 8.08/1.50  --bmc1_symbol_reachability              true
% 8.08/1.50  --bmc1_property_lemmas                  false
% 8.08/1.50  --bmc1_k_induction                      false
% 8.08/1.50  --bmc1_non_equiv_states                 false
% 8.08/1.50  --bmc1_deadlock                         false
% 8.08/1.50  --bmc1_ucm                              false
% 8.08/1.50  --bmc1_add_unsat_core                   none
% 8.08/1.50  --bmc1_unsat_core_children              false
% 8.08/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.08/1.50  --bmc1_out_stat                         full
% 8.08/1.50  --bmc1_ground_init                      false
% 8.08/1.50  --bmc1_pre_inst_next_state              false
% 8.08/1.50  --bmc1_pre_inst_state                   false
% 8.08/1.50  --bmc1_pre_inst_reach_state             false
% 8.08/1.50  --bmc1_out_unsat_core                   false
% 8.08/1.50  --bmc1_aig_witness_out                  false
% 8.08/1.50  --bmc1_verbose                          false
% 8.08/1.50  --bmc1_dump_clauses_tptp                false
% 8.08/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.08/1.50  --bmc1_dump_file                        -
% 8.08/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.08/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.08/1.50  --bmc1_ucm_extend_mode                  1
% 8.08/1.50  --bmc1_ucm_init_mode                    2
% 8.08/1.50  --bmc1_ucm_cone_mode                    none
% 8.08/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.08/1.50  --bmc1_ucm_relax_model                  4
% 8.08/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.08/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.08/1.50  --bmc1_ucm_layered_model                none
% 8.08/1.50  --bmc1_ucm_max_lemma_size               10
% 8.08/1.50  
% 8.08/1.50  ------ AIG Options
% 8.08/1.50  
% 8.08/1.50  --aig_mode                              false
% 8.08/1.50  
% 8.08/1.50  ------ Instantiation Options
% 8.08/1.50  
% 8.08/1.50  --instantiation_flag                    true
% 8.08/1.50  --inst_sos_flag                         true
% 8.08/1.50  --inst_sos_phase                        true
% 8.08/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.08/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.08/1.50  --inst_lit_sel_side                     num_symb
% 8.08/1.50  --inst_solver_per_active                1400
% 8.08/1.50  --inst_solver_calls_frac                1.
% 8.08/1.50  --inst_passive_queue_type               priority_queues
% 8.08/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.08/1.50  --inst_passive_queues_freq              [25;2]
% 8.08/1.50  --inst_dismatching                      true
% 8.08/1.50  --inst_eager_unprocessed_to_passive     true
% 8.08/1.50  --inst_prop_sim_given                   true
% 8.08/1.50  --inst_prop_sim_new                     false
% 8.08/1.50  --inst_subs_new                         false
% 8.08/1.50  --inst_eq_res_simp                      false
% 8.08/1.50  --inst_subs_given                       false
% 8.08/1.50  --inst_orphan_elimination               true
% 8.08/1.50  --inst_learning_loop_flag               true
% 8.08/1.50  --inst_learning_start                   3000
% 8.08/1.50  --inst_learning_factor                  2
% 8.08/1.50  --inst_start_prop_sim_after_learn       3
% 8.08/1.50  --inst_sel_renew                        solver
% 8.08/1.50  --inst_lit_activity_flag                true
% 8.08/1.50  --inst_restr_to_given                   false
% 8.08/1.50  --inst_activity_threshold               500
% 8.08/1.50  --inst_out_proof                        true
% 8.08/1.50  
% 8.08/1.50  ------ Resolution Options
% 8.08/1.50  
% 8.08/1.50  --resolution_flag                       true
% 8.08/1.50  --res_lit_sel                           adaptive
% 8.08/1.50  --res_lit_sel_side                      none
% 8.08/1.50  --res_ordering                          kbo
% 8.08/1.50  --res_to_prop_solver                    active
% 8.08/1.50  --res_prop_simpl_new                    false
% 8.08/1.50  --res_prop_simpl_given                  true
% 8.08/1.50  --res_passive_queue_type                priority_queues
% 8.08/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.08/1.50  --res_passive_queues_freq               [15;5]
% 8.08/1.50  --res_forward_subs                      full
% 8.08/1.50  --res_backward_subs                     full
% 8.08/1.50  --res_forward_subs_resolution           true
% 8.08/1.50  --res_backward_subs_resolution          true
% 8.08/1.50  --res_orphan_elimination                true
% 8.08/1.50  --res_time_limit                        2.
% 8.08/1.50  --res_out_proof                         true
% 8.08/1.50  
% 8.08/1.50  ------ Superposition Options
% 8.08/1.50  
% 8.08/1.50  --superposition_flag                    true
% 8.08/1.50  --sup_passive_queue_type                priority_queues
% 8.08/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.08/1.50  --sup_passive_queues_freq               [8;1;4]
% 8.08/1.50  --demod_completeness_check              fast
% 8.08/1.50  --demod_use_ground                      true
% 8.08/1.50  --sup_to_prop_solver                    passive
% 8.08/1.50  --sup_prop_simpl_new                    true
% 8.08/1.50  --sup_prop_simpl_given                  true
% 8.08/1.50  --sup_fun_splitting                     true
% 8.08/1.50  --sup_smt_interval                      50000
% 8.08/1.50  
% 8.08/1.50  ------ Superposition Simplification Setup
% 8.08/1.50  
% 8.08/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.08/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.08/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.08/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.08/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.08/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.08/1.50  --sup_immed_triv                        [TrivRules]
% 8.08/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.08/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.08/1.50  --sup_immed_bw_main                     []
% 8.08/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.08/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.08/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.08/1.50  --sup_input_bw                          []
% 8.08/1.50  
% 8.08/1.50  ------ Combination Options
% 8.08/1.50  
% 8.08/1.50  --comb_res_mult                         3
% 8.08/1.50  --comb_sup_mult                         2
% 8.08/1.50  --comb_inst_mult                        10
% 8.08/1.50  
% 8.08/1.50  ------ Debug Options
% 8.08/1.50  
% 8.08/1.50  --dbg_backtrace                         false
% 8.08/1.50  --dbg_dump_prop_clauses                 false
% 8.08/1.50  --dbg_dump_prop_clauses_file            -
% 8.08/1.50  --dbg_out_stat                          false
% 8.08/1.50  ------ Parsing...
% 8.08/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.08/1.50  
% 8.08/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 8.08/1.50  
% 8.08/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.08/1.50  
% 8.08/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.08/1.50  ------ Proving...
% 8.08/1.50  ------ Problem Properties 
% 8.08/1.50  
% 8.08/1.50  
% 8.08/1.50  clauses                                 29
% 8.08/1.50  conjectures                             1
% 8.08/1.50  EPR                                     3
% 8.08/1.50  Horn                                    23
% 8.08/1.50  unary                                   10
% 8.08/1.50  binary                                  10
% 8.08/1.50  lits                                    58
% 8.08/1.50  lits eq                                 14
% 8.08/1.50  fd_pure                                 0
% 8.08/1.50  fd_pseudo                               0
% 8.08/1.50  fd_cond                                 0
% 8.08/1.50  fd_pseudo_cond                          4
% 8.08/1.50  AC symbols                              0
% 8.08/1.50  
% 8.08/1.50  ------ Schedule dynamic 5 is on 
% 8.08/1.50  
% 8.08/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.08/1.50  
% 8.08/1.50  
% 8.08/1.50  ------ 
% 8.08/1.50  Current options:
% 8.08/1.50  ------ 
% 8.08/1.50  
% 8.08/1.50  ------ Input Options
% 8.08/1.50  
% 8.08/1.50  --out_options                           all
% 8.08/1.50  --tptp_safe_out                         true
% 8.08/1.50  --problem_path                          ""
% 8.08/1.50  --include_path                          ""
% 8.08/1.50  --clausifier                            res/vclausify_rel
% 8.08/1.50  --clausifier_options                    ""
% 8.08/1.50  --stdin                                 false
% 8.08/1.50  --stats_out                             all
% 8.08/1.50  
% 8.08/1.50  ------ General Options
% 8.08/1.50  
% 8.08/1.50  --fof                                   false
% 8.08/1.50  --time_out_real                         305.
% 8.08/1.50  --time_out_virtual                      -1.
% 8.08/1.50  --symbol_type_check                     false
% 8.08/1.50  --clausify_out                          false
% 8.08/1.50  --sig_cnt_out                           false
% 8.08/1.50  --trig_cnt_out                          false
% 8.08/1.50  --trig_cnt_out_tolerance                1.
% 8.08/1.50  --trig_cnt_out_sk_spl                   false
% 8.08/1.50  --abstr_cl_out                          false
% 8.08/1.50  
% 8.08/1.50  ------ Global Options
% 8.08/1.50  
% 8.08/1.50  --schedule                              default
% 8.08/1.50  --add_important_lit                     false
% 8.08/1.50  --prop_solver_per_cl                    1000
% 8.08/1.50  --min_unsat_core                        false
% 8.08/1.50  --soft_assumptions                      false
% 8.08/1.50  --soft_lemma_size                       3
% 8.08/1.50  --prop_impl_unit_size                   0
% 8.08/1.50  --prop_impl_unit                        []
% 8.08/1.50  --share_sel_clauses                     true
% 8.08/1.50  --reset_solvers                         false
% 8.08/1.50  --bc_imp_inh                            [conj_cone]
% 8.08/1.50  --conj_cone_tolerance                   3.
% 8.08/1.50  --extra_neg_conj                        none
% 8.08/1.50  --large_theory_mode                     true
% 8.08/1.50  --prolific_symb_bound                   200
% 8.08/1.50  --lt_threshold                          2000
% 8.08/1.50  --clause_weak_htbl                      true
% 8.08/1.50  --gc_record_bc_elim                     false
% 8.08/1.50  
% 8.08/1.50  ------ Preprocessing Options
% 8.08/1.50  
% 8.08/1.50  --preprocessing_flag                    true
% 8.08/1.50  --time_out_prep_mult                    0.1
% 8.08/1.50  --splitting_mode                        input
% 8.08/1.50  --splitting_grd                         true
% 8.08/1.50  --splitting_cvd                         false
% 8.08/1.50  --splitting_cvd_svl                     false
% 8.08/1.50  --splitting_nvd                         32
% 8.08/1.50  --sub_typing                            true
% 8.08/1.50  --prep_gs_sim                           true
% 8.08/1.50  --prep_unflatten                        true
% 8.08/1.50  --prep_res_sim                          true
% 8.08/1.50  --prep_upred                            true
% 8.08/1.50  --prep_sem_filter                       exhaustive
% 8.08/1.50  --prep_sem_filter_out                   false
% 8.08/1.50  --pred_elim                             true
% 8.08/1.50  --res_sim_input                         true
% 8.08/1.50  --eq_ax_congr_red                       true
% 8.08/1.50  --pure_diseq_elim                       true
% 8.08/1.50  --brand_transform                       false
% 8.08/1.50  --non_eq_to_eq                          false
% 8.08/1.50  --prep_def_merge                        true
% 8.08/1.50  --prep_def_merge_prop_impl              false
% 8.08/1.50  --prep_def_merge_mbd                    true
% 8.08/1.50  --prep_def_merge_tr_red                 false
% 8.08/1.50  --prep_def_merge_tr_cl                  false
% 8.08/1.50  --smt_preprocessing                     true
% 8.08/1.50  --smt_ac_axioms                         fast
% 8.08/1.50  --preprocessed_out                      false
% 8.08/1.50  --preprocessed_stats                    false
% 8.08/1.50  
% 8.08/1.50  ------ Abstraction refinement Options
% 8.08/1.50  
% 8.08/1.50  --abstr_ref                             []
% 8.08/1.50  --abstr_ref_prep                        false
% 8.08/1.50  --abstr_ref_until_sat                   false
% 8.08/1.50  --abstr_ref_sig_restrict                funpre
% 8.08/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.08/1.50  --abstr_ref_under                       []
% 8.08/1.50  
% 8.08/1.50  ------ SAT Options
% 8.08/1.50  
% 8.08/1.50  --sat_mode                              false
% 8.08/1.50  --sat_fm_restart_options                ""
% 8.08/1.50  --sat_gr_def                            false
% 8.08/1.50  --sat_epr_types                         true
% 8.08/1.50  --sat_non_cyclic_types                  false
% 8.08/1.50  --sat_finite_models                     false
% 8.08/1.50  --sat_fm_lemmas                         false
% 8.08/1.50  --sat_fm_prep                           false
% 8.08/1.50  --sat_fm_uc_incr                        true
% 8.08/1.50  --sat_out_model                         small
% 8.08/1.50  --sat_out_clauses                       false
% 8.08/1.50  
% 8.08/1.50  ------ QBF Options
% 8.08/1.50  
% 8.08/1.50  --qbf_mode                              false
% 8.08/1.50  --qbf_elim_univ                         false
% 8.08/1.50  --qbf_dom_inst                          none
% 8.08/1.50  --qbf_dom_pre_inst                      false
% 8.08/1.50  --qbf_sk_in                             false
% 8.08/1.50  --qbf_pred_elim                         true
% 8.08/1.50  --qbf_split                             512
% 8.08/1.50  
% 8.08/1.50  ------ BMC1 Options
% 8.08/1.50  
% 8.08/1.50  --bmc1_incremental                      false
% 8.08/1.50  --bmc1_axioms                           reachable_all
% 8.08/1.50  --bmc1_min_bound                        0
% 8.08/1.50  --bmc1_max_bound                        -1
% 8.08/1.50  --bmc1_max_bound_default                -1
% 8.08/1.50  --bmc1_symbol_reachability              true
% 8.08/1.50  --bmc1_property_lemmas                  false
% 8.08/1.50  --bmc1_k_induction                      false
% 8.08/1.50  --bmc1_non_equiv_states                 false
% 8.08/1.50  --bmc1_deadlock                         false
% 8.08/1.50  --bmc1_ucm                              false
% 8.08/1.50  --bmc1_add_unsat_core                   none
% 8.08/1.50  --bmc1_unsat_core_children              false
% 8.08/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.08/1.50  --bmc1_out_stat                         full
% 8.08/1.50  --bmc1_ground_init                      false
% 8.08/1.50  --bmc1_pre_inst_next_state              false
% 8.08/1.50  --bmc1_pre_inst_state                   false
% 8.08/1.50  --bmc1_pre_inst_reach_state             false
% 8.08/1.50  --bmc1_out_unsat_core                   false
% 8.08/1.50  --bmc1_aig_witness_out                  false
% 8.08/1.50  --bmc1_verbose                          false
% 8.08/1.50  --bmc1_dump_clauses_tptp                false
% 8.08/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.08/1.50  --bmc1_dump_file                        -
% 8.08/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.08/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.08/1.50  --bmc1_ucm_extend_mode                  1
% 8.08/1.50  --bmc1_ucm_init_mode                    2
% 8.08/1.50  --bmc1_ucm_cone_mode                    none
% 8.08/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.08/1.50  --bmc1_ucm_relax_model                  4
% 8.08/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.08/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.08/1.50  --bmc1_ucm_layered_model                none
% 8.08/1.50  --bmc1_ucm_max_lemma_size               10
% 8.08/1.50  
% 8.08/1.50  ------ AIG Options
% 8.08/1.50  
% 8.08/1.50  --aig_mode                              false
% 8.08/1.50  
% 8.08/1.50  ------ Instantiation Options
% 8.08/1.50  
% 8.08/1.50  --instantiation_flag                    true
% 8.08/1.50  --inst_sos_flag                         true
% 8.08/1.50  --inst_sos_phase                        true
% 8.08/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.08/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.08/1.50  --inst_lit_sel_side                     none
% 8.08/1.50  --inst_solver_per_active                1400
% 8.08/1.50  --inst_solver_calls_frac                1.
% 8.08/1.50  --inst_passive_queue_type               priority_queues
% 8.08/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.08/1.50  --inst_passive_queues_freq              [25;2]
% 8.08/1.50  --inst_dismatching                      true
% 8.08/1.50  --inst_eager_unprocessed_to_passive     true
% 8.08/1.50  --inst_prop_sim_given                   true
% 8.08/1.50  --inst_prop_sim_new                     false
% 8.08/1.50  --inst_subs_new                         false
% 8.08/1.50  --inst_eq_res_simp                      false
% 8.08/1.50  --inst_subs_given                       false
% 8.08/1.50  --inst_orphan_elimination               true
% 8.08/1.50  --inst_learning_loop_flag               true
% 8.08/1.50  --inst_learning_start                   3000
% 8.08/1.50  --inst_learning_factor                  2
% 8.08/1.50  --inst_start_prop_sim_after_learn       3
% 8.08/1.50  --inst_sel_renew                        solver
% 8.08/1.50  --inst_lit_activity_flag                true
% 8.08/1.50  --inst_restr_to_given                   false
% 8.08/1.50  --inst_activity_threshold               500
% 8.08/1.50  --inst_out_proof                        true
% 8.08/1.50  
% 8.08/1.50  ------ Resolution Options
% 8.08/1.50  
% 8.08/1.50  --resolution_flag                       false
% 8.08/1.50  --res_lit_sel                           adaptive
% 8.08/1.50  --res_lit_sel_side                      none
% 8.08/1.50  --res_ordering                          kbo
% 8.08/1.50  --res_to_prop_solver                    active
% 8.08/1.50  --res_prop_simpl_new                    false
% 8.08/1.50  --res_prop_simpl_given                  true
% 8.08/1.50  --res_passive_queue_type                priority_queues
% 8.08/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.08/1.50  --res_passive_queues_freq               [15;5]
% 8.08/1.50  --res_forward_subs                      full
% 8.08/1.50  --res_backward_subs                     full
% 8.08/1.50  --res_forward_subs_resolution           true
% 8.08/1.50  --res_backward_subs_resolution          true
% 8.08/1.50  --res_orphan_elimination                true
% 8.08/1.50  --res_time_limit                        2.
% 8.08/1.50  --res_out_proof                         true
% 8.08/1.50  
% 8.08/1.50  ------ Superposition Options
% 8.08/1.50  
% 8.08/1.50  --superposition_flag                    true
% 8.08/1.50  --sup_passive_queue_type                priority_queues
% 8.08/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.08/1.50  --sup_passive_queues_freq               [8;1;4]
% 8.08/1.50  --demod_completeness_check              fast
% 8.08/1.50  --demod_use_ground                      true
% 8.08/1.50  --sup_to_prop_solver                    passive
% 8.08/1.50  --sup_prop_simpl_new                    true
% 8.08/1.50  --sup_prop_simpl_given                  true
% 8.08/1.50  --sup_fun_splitting                     true
% 8.08/1.50  --sup_smt_interval                      50000
% 8.08/1.50  
% 8.08/1.50  ------ Superposition Simplification Setup
% 8.08/1.50  
% 8.08/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.08/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.08/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.08/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.08/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.08/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.08/1.50  --sup_immed_triv                        [TrivRules]
% 8.08/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.08/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.08/1.50  --sup_immed_bw_main                     []
% 8.08/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.08/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.08/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.08/1.50  --sup_input_bw                          []
% 8.08/1.50  
% 8.08/1.50  ------ Combination Options
% 8.08/1.50  
% 8.08/1.50  --comb_res_mult                         3
% 8.08/1.50  --comb_sup_mult                         2
% 8.08/1.50  --comb_inst_mult                        10
% 8.08/1.50  
% 8.08/1.50  ------ Debug Options
% 8.08/1.50  
% 8.08/1.50  --dbg_backtrace                         false
% 8.08/1.50  --dbg_dump_prop_clauses                 false
% 8.08/1.50  --dbg_dump_prop_clauses_file            -
% 8.08/1.50  --dbg_out_stat                          false
% 8.08/1.50  
% 8.08/1.50  
% 8.08/1.50  
% 8.08/1.50  
% 8.08/1.50  ------ Proving...
% 8.08/1.50  
% 8.08/1.50  
% 8.08/1.50  % SZS status Theorem for theBenchmark.p
% 8.08/1.50  
% 8.08/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 8.08/1.50  
% 8.08/1.50  fof(f12,axiom,(
% 8.08/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f27,plain,(
% 8.08/1.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.08/1.50    inference(ennf_transformation,[],[f12])).
% 8.08/1.50  
% 8.08/1.50  fof(f74,plain,(
% 8.08/1.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.08/1.50    inference(cnf_transformation,[],[f27])).
% 8.08/1.50  
% 8.08/1.50  fof(f22,conjecture,(
% 8.08/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f23,negated_conjecture,(
% 8.08/1.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 8.08/1.50    inference(negated_conjecture,[],[f22])).
% 8.08/1.50  
% 8.08/1.50  fof(f36,plain,(
% 8.08/1.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.08/1.50    inference(ennf_transformation,[],[f23])).
% 8.08/1.50  
% 8.08/1.50  fof(f49,plain,(
% 8.08/1.50    ? [X0] : (? [X1] : (((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.08/1.50    inference(nnf_transformation,[],[f36])).
% 8.08/1.50  
% 8.08/1.50  fof(f50,plain,(
% 8.08/1.50    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.08/1.50    inference(flattening,[],[f49])).
% 8.08/1.50  
% 8.08/1.50  fof(f52,plain,(
% 8.08/1.50    ( ! [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK3),X0) | ~v4_pre_topc(sK3,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK3),X0) | v4_pre_topc(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 8.08/1.50    introduced(choice_axiom,[])).
% 8.08/1.50  
% 8.08/1.50  fof(f51,plain,(
% 8.08/1.50    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X1),sK2) | ~v4_pre_topc(X1,sK2)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X1),sK2) | v4_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 8.08/1.50    introduced(choice_axiom,[])).
% 8.08/1.50  
% 8.08/1.50  fof(f53,plain,(
% 8.08/1.50    ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) | ~v4_pre_topc(sK3,sK2)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) | v4_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 8.08/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f50,f52,f51])).
% 8.08/1.50  
% 8.08/1.50  fof(f86,plain,(
% 8.08/1.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 8.08/1.50    inference(cnf_transformation,[],[f53])).
% 8.08/1.50  
% 8.08/1.50  fof(f21,axiom,(
% 8.08/1.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f35,plain,(
% 8.08/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 8.08/1.50    inference(ennf_transformation,[],[f21])).
% 8.08/1.50  
% 8.08/1.50  fof(f84,plain,(
% 8.08/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 8.08/1.50    inference(cnf_transformation,[],[f35])).
% 8.08/1.50  
% 8.08/1.50  fof(f19,axiom,(
% 8.08/1.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f33,plain,(
% 8.08/1.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 8.08/1.50    inference(ennf_transformation,[],[f19])).
% 8.08/1.50  
% 8.08/1.50  fof(f81,plain,(
% 8.08/1.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 8.08/1.50    inference(cnf_transformation,[],[f33])).
% 8.08/1.50  
% 8.08/1.50  fof(f85,plain,(
% 8.08/1.50    l1_pre_topc(sK2)),
% 8.08/1.50    inference(cnf_transformation,[],[f53])).
% 8.08/1.50  
% 8.08/1.50  fof(f10,axiom,(
% 8.08/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f26,plain,(
% 8.08/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.08/1.50    inference(ennf_transformation,[],[f10])).
% 8.08/1.50  
% 8.08/1.50  fof(f72,plain,(
% 8.08/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.08/1.50    inference(cnf_transformation,[],[f26])).
% 8.08/1.50  
% 8.08/1.50  fof(f4,axiom,(
% 8.08/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f66,plain,(
% 8.08/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.08/1.50    inference(cnf_transformation,[],[f4])).
% 8.08/1.50  
% 8.08/1.50  fof(f97,plain,(
% 8.08/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.08/1.50    inference(definition_unfolding,[],[f72,f66])).
% 8.08/1.50  
% 8.08/1.50  fof(f6,axiom,(
% 8.08/1.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f68,plain,(
% 8.08/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 8.08/1.50    inference(cnf_transformation,[],[f6])).
% 8.08/1.50  
% 8.08/1.50  fof(f89,plain,(
% 8.08/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 8.08/1.50    inference(definition_unfolding,[],[f68,f66,f66])).
% 8.08/1.50  
% 8.08/1.50  fof(f11,axiom,(
% 8.08/1.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f73,plain,(
% 8.08/1.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 8.08/1.50    inference(cnf_transformation,[],[f11])).
% 8.08/1.50  
% 8.08/1.50  fof(f9,axiom,(
% 8.08/1.50    ! [X0] : k2_subset_1(X0) = X0),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f71,plain,(
% 8.08/1.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 8.08/1.50    inference(cnf_transformation,[],[f9])).
% 8.08/1.50  
% 8.08/1.50  fof(f15,axiom,(
% 8.08/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f30,plain,(
% 8.08/1.50    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.08/1.50    inference(ennf_transformation,[],[f15])).
% 8.08/1.50  
% 8.08/1.50  fof(f77,plain,(
% 8.08/1.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.08/1.50    inference(cnf_transformation,[],[f30])).
% 8.08/1.50  
% 8.08/1.50  fof(f8,axiom,(
% 8.08/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f25,plain,(
% 8.08/1.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 8.08/1.50    inference(ennf_transformation,[],[f8])).
% 8.08/1.50  
% 8.08/1.50  fof(f70,plain,(
% 8.08/1.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 8.08/1.50    inference(cnf_transformation,[],[f25])).
% 8.08/1.50  
% 8.08/1.50  fof(f14,axiom,(
% 8.08/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f29,plain,(
% 8.08/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 8.08/1.50    inference(ennf_transformation,[],[f14])).
% 8.08/1.50  
% 8.08/1.50  fof(f76,plain,(
% 8.08/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 8.08/1.50    inference(cnf_transformation,[],[f29])).
% 8.08/1.50  
% 8.08/1.50  fof(f1,axiom,(
% 8.08/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f24,plain,(
% 8.08/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 8.08/1.50    inference(ennf_transformation,[],[f1])).
% 8.08/1.50  
% 8.08/1.50  fof(f37,plain,(
% 8.08/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 8.08/1.50    inference(nnf_transformation,[],[f24])).
% 8.08/1.50  
% 8.08/1.50  fof(f38,plain,(
% 8.08/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.08/1.50    inference(rectify,[],[f37])).
% 8.08/1.50  
% 8.08/1.50  fof(f39,plain,(
% 8.08/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 8.08/1.50    introduced(choice_axiom,[])).
% 8.08/1.50  
% 8.08/1.50  fof(f40,plain,(
% 8.08/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.08/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 8.08/1.50  
% 8.08/1.50  fof(f55,plain,(
% 8.08/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 8.08/1.50    inference(cnf_transformation,[],[f40])).
% 8.08/1.50  
% 8.08/1.50  fof(f7,axiom,(
% 8.08/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f69,plain,(
% 8.08/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 8.08/1.50    inference(cnf_transformation,[],[f7])).
% 8.08/1.50  
% 8.08/1.50  fof(f17,axiom,(
% 8.08/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f79,plain,(
% 8.08/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 8.08/1.50    inference(cnf_transformation,[],[f17])).
% 8.08/1.50  
% 8.08/1.50  fof(f2,axiom,(
% 8.08/1.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f41,plain,(
% 8.08/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 8.08/1.50    inference(nnf_transformation,[],[f2])).
% 8.08/1.50  
% 8.08/1.50  fof(f42,plain,(
% 8.08/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 8.08/1.50    inference(flattening,[],[f41])).
% 8.08/1.50  
% 8.08/1.50  fof(f43,plain,(
% 8.08/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 8.08/1.50    inference(rectify,[],[f42])).
% 8.08/1.50  
% 8.08/1.50  fof(f44,plain,(
% 8.08/1.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 8.08/1.50    introduced(choice_axiom,[])).
% 8.08/1.50  
% 8.08/1.50  fof(f45,plain,(
% 8.08/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 8.08/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 8.08/1.50  
% 8.08/1.50  fof(f59,plain,(
% 8.08/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 8.08/1.50    inference(cnf_transformation,[],[f45])).
% 8.08/1.50  
% 8.08/1.50  fof(f93,plain,(
% 8.08/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 8.08/1.50    inference(definition_unfolding,[],[f59,f66])).
% 8.08/1.50  
% 8.08/1.50  fof(f98,plain,(
% 8.08/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 8.08/1.50    inference(equality_resolution,[],[f93])).
% 8.08/1.50  
% 8.08/1.50  fof(f60,plain,(
% 8.08/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.08/1.50    inference(cnf_transformation,[],[f45])).
% 8.08/1.50  
% 8.08/1.50  fof(f92,plain,(
% 8.08/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.08/1.50    inference(definition_unfolding,[],[f60,f66])).
% 8.08/1.50  
% 8.08/1.50  fof(f13,axiom,(
% 8.08/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f28,plain,(
% 8.08/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.08/1.50    inference(ennf_transformation,[],[f13])).
% 8.08/1.50  
% 8.08/1.50  fof(f75,plain,(
% 8.08/1.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.08/1.50    inference(cnf_transformation,[],[f28])).
% 8.08/1.50  
% 8.08/1.50  fof(f61,plain,(
% 8.08/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.08/1.50    inference(cnf_transformation,[],[f45])).
% 8.08/1.50  
% 8.08/1.50  fof(f91,plain,(
% 8.08/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 8.08/1.50    inference(definition_unfolding,[],[f61,f66])).
% 8.08/1.50  
% 8.08/1.50  fof(f57,plain,(
% 8.08/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 8.08/1.50    inference(cnf_transformation,[],[f45])).
% 8.08/1.50  
% 8.08/1.50  fof(f95,plain,(
% 8.08/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 8.08/1.50    inference(definition_unfolding,[],[f57,f66])).
% 8.08/1.50  
% 8.08/1.50  fof(f100,plain,(
% 8.08/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 8.08/1.50    inference(equality_resolution,[],[f95])).
% 8.08/1.50  
% 8.08/1.50  fof(f58,plain,(
% 8.08/1.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 8.08/1.50    inference(cnf_transformation,[],[f45])).
% 8.08/1.50  
% 8.08/1.50  fof(f94,plain,(
% 8.08/1.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 8.08/1.50    inference(definition_unfolding,[],[f58,f66])).
% 8.08/1.50  
% 8.08/1.50  fof(f99,plain,(
% 8.08/1.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 8.08/1.50    inference(equality_resolution,[],[f94])).
% 8.08/1.50  
% 8.08/1.50  fof(f5,axiom,(
% 8.08/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f67,plain,(
% 8.08/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.08/1.50    inference(cnf_transformation,[],[f5])).
% 8.08/1.50  
% 8.08/1.50  fof(f96,plain,(
% 8.08/1.50    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 8.08/1.50    inference(definition_unfolding,[],[f67,f66])).
% 8.08/1.50  
% 8.08/1.50  fof(f3,axiom,(
% 8.08/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f46,plain,(
% 8.08/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.08/1.50    inference(nnf_transformation,[],[f3])).
% 8.08/1.50  
% 8.08/1.50  fof(f47,plain,(
% 8.08/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.08/1.50    inference(flattening,[],[f46])).
% 8.08/1.50  
% 8.08/1.50  fof(f65,plain,(
% 8.08/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 8.08/1.50    inference(cnf_transformation,[],[f47])).
% 8.08/1.50  
% 8.08/1.50  fof(f56,plain,(
% 8.08/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 8.08/1.50    inference(cnf_transformation,[],[f40])).
% 8.08/1.50  
% 8.08/1.50  fof(f88,plain,(
% 8.08/1.50    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) | ~v4_pre_topc(sK3,sK2)),
% 8.08/1.50    inference(cnf_transformation,[],[f53])).
% 8.08/1.50  
% 8.08/1.50  fof(f20,axiom,(
% 8.08/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 8.08/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.08/1.50  
% 8.08/1.50  fof(f34,plain,(
% 8.08/1.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.08/1.50    inference(ennf_transformation,[],[f20])).
% 8.08/1.50  
% 8.08/1.50  fof(f48,plain,(
% 8.08/1.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.08/1.50    inference(nnf_transformation,[],[f34])).
% 8.08/1.50  
% 8.08/1.50  fof(f83,plain,(
% 8.08/1.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.08/1.50    inference(cnf_transformation,[],[f48])).
% 8.08/1.50  
% 8.08/1.50  fof(f87,plain,(
% 8.08/1.50    v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) | v4_pre_topc(sK3,sK2)),
% 8.08/1.50    inference(cnf_transformation,[],[f53])).
% 8.08/1.50  
% 8.08/1.50  fof(f82,plain,(
% 8.08/1.50    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.08/1.50    inference(cnf_transformation,[],[f48])).
% 8.08/1.50  
% 8.08/1.50  cnf(c_19,plain,
% 8.08/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.08/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 8.08/1.50      inference(cnf_transformation,[],[f74]) ).
% 8.08/1.50  
% 8.08/1.50  cnf(c_1237,plain,
% 8.08/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.08/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 8.08/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.08/1.50  
% 8.08/1.50  cnf(c_32,negated_conjecture,
% 8.08/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 8.08/1.50      inference(cnf_transformation,[],[f86]) ).
% 8.08/1.50  
% 8.08/1.50  cnf(c_1231,plain,
% 8.08/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 8.08/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 8.08/1.50  
% 8.08/1.50  cnf(c_29,plain,
% 8.08/1.50      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 8.08/1.50      inference(cnf_transformation,[],[f84]) ).
% 8.08/1.50  
% 8.08/1.50  cnf(c_26,plain,
% 8.08/1.50      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 8.08/1.50      inference(cnf_transformation,[],[f81]) ).
% 8.08/1.50  
% 8.08/1.50  cnf(c_389,plain,
% 8.08/1.50      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 8.08/1.50      inference(resolution,[status(thm)],[c_29,c_26]) ).
% 8.08/1.50  
% 8.08/1.50  cnf(c_33,negated_conjecture,
% 8.08/1.50      ( l1_pre_topc(sK2) ),
% 8.08/1.50      inference(cnf_transformation,[],[f85]) ).
% 8.08/1.50  
% 8.08/1.50  cnf(c_403,plain,
% 8.08/1.50      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 8.08/1.50      inference(resolution_lifted,[status(thm)],[c_389,c_33]) ).
% 8.08/1.50  
% 8.08/1.50  cnf(c_404,plain,
% 8.08/1.50      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 8.08/1.50      inference(unflattening,[status(thm)],[c_403]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1252,plain,
% 8.08/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_1231,c_404]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_17,plain,
% 8.08/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.08/1.51      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 8.08/1.51      inference(cnf_transformation,[],[f97]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1239,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 8.08/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_3992,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,X1))) = k3_subset_1(X0,k3_subset_1(X0,X1))
% 8.08/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1237,c_1239]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10247,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) = k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1252,c_3992]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_3994,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)) = k3_subset_1(k2_struct_0(sK2),sK3) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1252,c_1239]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_0,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 8.08/1.51      inference(cnf_transformation,[],[f89]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4006,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) = k3_xboole_0(k2_struct_0(sK2),sK3) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_3994,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10251,plain,
% 8.08/1.51      ( k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)) = k3_xboole_0(k2_struct_0(sK2),sK3) ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_10247,c_4006]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10385,plain,
% 8.08/1.51      ( m1_subset_1(k3_subset_1(k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 8.08/1.51      | m1_subset_1(k3_xboole_0(k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_10251,c_1237]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10554,plain,
% 8.08/1.51      ( m1_subset_1(k3_xboole_0(k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 8.08/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1237,c_10385]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_17522,plain,
% 8.08/1.51      ( m1_subset_1(k3_xboole_0(k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 8.08/1.51      inference(global_propositional_subsumption,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_10554,c_1252]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_18,plain,
% 8.08/1.51      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 8.08/1.51      inference(cnf_transformation,[],[f73]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1238,plain,
% 8.08/1.51      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_16,plain,
% 8.08/1.51      ( k2_subset_1(X0) = X0 ),
% 8.08/1.51      inference(cnf_transformation,[],[f71]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1253,plain,
% 8.08/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_1238,c_16]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_22,plain,
% 8.08/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.08/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 8.08/1.51      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 8.08/1.51      inference(cnf_transformation,[],[f77]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1234,plain,
% 8.08/1.51      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 8.08/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 8.08/1.51      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2099,plain,
% 8.08/1.51      ( k9_subset_1(X0,X0,k3_subset_1(X0,X1)) = k7_subset_1(X0,X0,X1)
% 8.08/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1253,c_1234]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_15,plain,
% 8.08/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.08/1.51      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 8.08/1.51      inference(cnf_transformation,[],[f70]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1240,plain,
% 8.08/1.51      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 8.08/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4414,plain,
% 8.08/1.51      ( k9_subset_1(X0,X0,X1) = k9_subset_1(X0,X1,X0) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1253,c_1240]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_21,plain,
% 8.08/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.08/1.51      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 8.08/1.51      inference(cnf_transformation,[],[f76]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1235,plain,
% 8.08/1.51      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 8.08/1.51      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2620,plain,
% 8.08/1.51      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1253,c_1235]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4416,plain,
% 8.08/1.51      ( k9_subset_1(X0,X0,X1) = k3_xboole_0(X1,X0) ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_4414,c_2620]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_33030,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(X0,X1),X0) = k7_subset_1(X0,X0,X1)
% 8.08/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_2099,c_4416]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_33039,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)),k2_struct_0(sK2)) = k7_subset_1(k2_struct_0(sK2),k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_17522,c_33030]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2,plain,
% 8.08/1.51      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 8.08/1.51      inference(cnf_transformation,[],[f55]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1250,plain,
% 8.08/1.51      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 8.08/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4413,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),sK3,X0) = k9_subset_1(k2_struct_0(sK2),X0,sK3) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1252,c_1240]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2619,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),X0,sK3) = k3_xboole_0(X0,sK3) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1252,c_1235]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4417,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),sK3,X0) = k3_xboole_0(X0,sK3) ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_4413,c_2619]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2098,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),X0)) = k7_subset_1(k2_struct_0(sK2),sK3,X0)
% 8.08/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1252,c_1234]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_3869,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),X0))) = k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),X0))
% 8.08/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1237,c_2098]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4214,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) = k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1252,c_3869]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4598,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),sK3) = k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4417,c_4214]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_14,plain,
% 8.08/1.51      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 8.08/1.51      inference(cnf_transformation,[],[f69]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_24,plain,
% 8.08/1.51      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
% 8.08/1.51      inference(cnf_transformation,[],[f79]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1641,plain,
% 8.08/1.51      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_14,c_24]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1781,plain,
% 8.08/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1641,c_24]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4691,plain,
% 8.08/1.51      ( k3_xboole_0(sK3,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) = k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4598,c_1781]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1785,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1781,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2236,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1785,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1645,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_0,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2847,plain,
% 8.08/1.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_2236,c_1645]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_7,plain,
% 8.08/1.51      ( ~ r2_hidden(X0,X1)
% 8.08/1.51      | r2_hidden(X0,X2)
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 8.08/1.51      inference(cnf_transformation,[],[f98]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1245,plain,
% 8.08/1.51      ( r2_hidden(X0,X1) != iProver_top
% 8.08/1.51      | r2_hidden(X0,X2) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_7930,plain,
% 8.08/1.51      ( r2_hidden(X0,X1) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_2847,c_1245]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_7948,plain,
% 8.08/1.51      ( r2_hidden(X0,X1) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(X1,X2)) = iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_7930,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_8604,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),sK3)) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4691,c_7948]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_8611,plain,
% 8.08/1.51      ( r2_hidden(X0,k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3))) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) = iProver_top ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_8604,c_4598]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10375,plain,
% 8.08/1.51      ( k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)) = k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_10251,c_4691]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_6,plain,
% 8.08/1.51      ( r2_hidden(sK1(X0,X1,X2),X0)
% 8.08/1.51      | r2_hidden(sK1(X0,X1,X2),X2)
% 8.08/1.51      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 8.08/1.51      inference(cnf_transformation,[],[f92]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1246,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 8.08/1.51      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 8.08/1.51      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_20,plain,
% 8.08/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.08/1.51      | ~ r2_hidden(X2,X0)
% 8.08/1.51      | r2_hidden(X2,X1) ),
% 8.08/1.51      inference(cnf_transformation,[],[f75]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1236,plain,
% 8.08/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.08/1.51      | r2_hidden(X2,X0) != iProver_top
% 8.08/1.51      | r2_hidden(X2,X1) = iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_3711,plain,
% 8.08/1.51      ( r2_hidden(X0,k2_struct_0(sK2)) = iProver_top
% 8.08/1.51      | r2_hidden(X0,sK3) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1252,c_1236]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_5,plain,
% 8.08/1.51      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 8.08/1.51      | r2_hidden(sK1(X0,X1,X2),X2)
% 8.08/1.51      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 8.08/1.51      inference(cnf_transformation,[],[f91]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1247,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 8.08/1.51      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 8.08/1.51      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_8878,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_struct_0(sK2))) = X1
% 8.08/1.51      | r2_hidden(sK1(X0,k2_struct_0(sK2),X1),X1) = iProver_top
% 8.08/1.51      | r2_hidden(sK1(X0,k2_struct_0(sK2),X1),sK3) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_3711,c_1247]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_8966,plain,
% 8.08/1.51      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2))) = X0
% 8.08/1.51      | r2_hidden(sK1(sK3,k2_struct_0(sK2),X0),X0) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1246,c_8878]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9,plain,
% 8.08/1.51      ( r2_hidden(X0,X1)
% 8.08/1.51      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 8.08/1.51      inference(cnf_transformation,[],[f100]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1243,plain,
% 8.08/1.51      ( r2_hidden(X0,X1) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4684,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4598,c_1243]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11739,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)))) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) = iProver_top ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_4684,c_10251,c_10375]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_7920,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k2_struct_0(sK2)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,sK3) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_3994,c_1245]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_8,plain,
% 8.08/1.51      ( ~ r2_hidden(X0,X1)
% 8.08/1.51      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 8.08/1.51      inference(cnf_transformation,[],[f99]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1244,plain,
% 8.08/1.51      ( r2_hidden(X0,X1) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4481,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4006,c_1244]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_8395,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k2_struct_0(sK2)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,sK3) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_7920,c_4481]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4133,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k2_struct_0(sK2)) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4006,c_1243]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9147,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,sK3) = iProver_top ),
% 8.08/1.51      inference(global_propositional_subsumption,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_8395,c_4133]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4685,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) != iProver_top
% 8.08/1.51      | r2_hidden(X0,sK3) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4598,c_1244]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10373,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) != iProver_top
% 8.08/1.51      | r2_hidden(X0,sK3) != iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_10251,c_4685]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10380,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)))) != iProver_top
% 8.08/1.51      | r2_hidden(X0,sK3) != iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_10373,c_10375]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11743,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)))) != iProver_top ),
% 8.08/1.51      inference(global_propositional_subsumption,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_11739,c_9147,c_10380]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_12700,plain,
% 8.08/1.51      ( k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))) = k5_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_8966,c_11743]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2330,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)) = k7_subset_1(k2_struct_0(sK2),sK3,sK3) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1252,c_2098]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4594,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),sK3) = k7_subset_1(k2_struct_0(sK2),sK3,sK3) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4417,c_2330]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4605,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),sK3))) = k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4594,c_1645]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4622,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3))) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_4605,c_4594]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4615,plain,
% 8.08/1.51      ( k3_xboole_0(sK3,k3_subset_1(k2_struct_0(sK2),sK3)) = k7_subset_1(k2_struct_0(sK2),sK3,sK3) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4594,c_1781]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4486,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_2847,c_1244]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4491,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_4486,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_6816,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3))) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),sK3)) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4615,c_4491]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_6819,plain,
% 8.08/1.51      ( r2_hidden(X0,k7_subset_1(k2_struct_0(sK2),sK3,sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3))) != iProver_top ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_6816,c_4594]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4480,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,sK3) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_3994,c_1244]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_7935,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3))) = iProver_top
% 8.08/1.51      | r2_hidden(X0,sK3) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4594,c_1245]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4607,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3)))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),sK3) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4594,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4621,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),sK3,sK3)))) = k7_subset_1(k2_struct_0(sK2),sK3,sK3) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_4607,c_4594]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9258,plain,
% 8.08/1.51      ( r2_hidden(X0,k7_subset_1(k2_struct_0(sK2),sK3,sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4621,c_1243]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9265,plain,
% 8.08/1.51      ( r2_hidden(X0,k7_subset_1(k2_struct_0(sK2),sK3,sK3)) != iProver_top ),
% 8.08/1.51      inference(global_propositional_subsumption,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_6819,c_4480,c_7935,c_9258]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9271,plain,
% 8.08/1.51      ( r1_tarski(k7_subset_1(k2_struct_0(sK2),sK3,sK3),X0) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1250,c_9265]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_13,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 8.08/1.51      inference(cnf_transformation,[],[f96]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1786,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1781,c_13]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1871,plain,
% 8.08/1.51      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1786,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1872,plain,
% 8.08/1.51      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_1871,c_1786]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4487,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1872,c_1244]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1874,plain,
% 8.08/1.51      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1872,c_13]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4490,plain,
% 8.08/1.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_4487,c_1874]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9528,plain,
% 8.08/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1250,c_4490]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10,plain,
% 8.08/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 8.08/1.51      inference(cnf_transformation,[],[f65]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1242,plain,
% 8.08/1.51      ( X0 = X1
% 8.08/1.51      | r1_tarski(X1,X0) != iProver_top
% 8.08/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9541,plain,
% 8.08/1.51      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_9528,c_1242]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10346,plain,
% 8.08/1.51      ( k7_subset_1(k2_struct_0(sK2),sK3,sK3) = k1_xboole_0 ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_9271,c_9541]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10921,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_4622,c_4622,c_10346]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10922,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) = k3_subset_1(k2_struct_0(sK2),sK3) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_10921,c_13]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10927,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)))) = k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_10922,c_1645]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10948,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_10927,c_10922]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_3868,plain,
% 8.08/1.51      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k3_xboole_0(X1,k3_subset_1(X0,X2))
% 8.08/1.51      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1237,c_1235]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9457,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),X0,k3_subset_1(k2_struct_0(sK2),sK3)) = k3_xboole_0(X0,k3_subset_1(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1252,c_3868]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_3866,plain,
% 8.08/1.51      ( k9_subset_1(X0,k3_subset_1(X0,X1),k3_subset_1(X0,X2)) = k7_subset_1(X0,k3_subset_1(X0,X1),X2)
% 8.08/1.51      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 8.08/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1237,c_1234]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_7311,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),X0)) = k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),X0)
% 8.08/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1252,c_3866]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_8173,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)) = k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1252,c_7311]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9803,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)) = k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_9457,c_8173]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1644,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9827,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3)) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_9803,c_1644]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10949,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0) ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_10948,c_9803,c_9827]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10983,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_10949,c_1244]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10997,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_10983,c_13]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10930,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_10922,c_1243]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11142,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top ),
% 8.08/1.51      inference(global_propositional_subsumption,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_10997,c_10930]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_12701,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)) = k5_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_8966,c_11142]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10926,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0),k3_subset_1(k2_struct_0(sK2),sK3)))) = k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_10922,c_2236]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10951,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0),k3_subset_1(k2_struct_0(sK2),sK3)))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0) ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_10926,c_9803,c_9827]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9814,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3))) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_9803,c_4491]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9836,plain,
% 8.08/1.51      ( r2_hidden(X0,k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) != iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_9814,c_9803,c_9827]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9815,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_9803,c_1244]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9835,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) != iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_9815,c_9827]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9812,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_9803,c_1243]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9838,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) != iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_9812,c_9827]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10010,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) != iProver_top ),
% 8.08/1.51      inference(global_propositional_subsumption,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_9836,c_9835,c_9838]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_10016,plain,
% 8.08/1.51      ( r1_tarski(k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0),X0) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1250,c_10010]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11228,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0) = k1_xboole_0 ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_10016,c_9541]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11364,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0),k3_subset_1(k2_struct_0(sK2),sK3)))) = k1_xboole_0 ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_10951,c_10951,c_11228]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11373,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0),k3_subset_1(k2_struct_0(sK2),sK3)))) = k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_11364,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2001,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,X0) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1644,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2107,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k3_xboole_0(X0,X0) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1781,c_2001]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2531,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_2107,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9825,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k1_xboole_0,k3_subset_1(k2_struct_0(sK2),sK3))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_9803,c_2531]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2110,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) = k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_2001,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9826,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k7_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3),sK3))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_9803,c_2110]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_9828,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k1_xboole_0,k3_subset_1(k2_struct_0(sK2),sK3))) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_9825,c_9826]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11389,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0)) = k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_11364,c_1785]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11390,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k1_xboole_0) = k3_subset_1(k2_struct_0(sK2),sK3) ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_11389,c_10922]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11559,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k1_xboole_0,k3_subset_1(k2_struct_0(sK2),sK3))) = k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_11373,c_9803,c_9827,c_9828,c_10922,c_11390]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11391,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)))) = k1_xboole_0 ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_11390,c_11364]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11392,plain,
% 8.08/1.51      ( k3_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_xboole_0(k1_xboole_0,k3_subset_1(k2_struct_0(sK2),sK3))) = k1_xboole_0 ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_11391,c_9803,c_9827,c_9828]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11560,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)) = k1_xboole_0 ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_11559,c_11392]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_12702,plain,
% 8.08/1.51      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2))) = k1_xboole_0 ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_12701,c_11560]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_12714,plain,
% 8.08/1.51      ( k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))) = k1_xboole_0 ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_12700,c_12702]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_15698,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_8611,c_10251,c_10375,c_12714]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_15702,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top ),
% 8.08/1.51      inference(global_propositional_subsumption,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_15698,c_4490]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_15703,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))) = iProver_top ),
% 8.08/1.51      inference(renaming,[status(thm)],[c_15702]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1,plain,
% 8.08/1.51      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 8.08/1.51      inference(cnf_transformation,[],[f56]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1251,plain,
% 8.08/1.51      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 8.08/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_15711,plain,
% 8.08/1.51      ( r2_hidden(sK0(X0,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))),k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r1_tarski(X0,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_15703,c_1251]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2677,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1781,c_1645]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4689,plain,
% 8.08/1.51      ( k3_xboole_0(sK3,k5_xboole_0(sK3,k3_xboole_0(sK3,k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))))) = k5_xboole_0(sK3,k3_xboole_0(sK3,k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4598,c_2677]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4693,plain,
% 8.08/1.51      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) = k3_xboole_0(sK3,k5_xboole_0(sK3,k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)))) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_4689,c_4691]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_18534,plain,
% 8.08/1.51      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)))) = k3_xboole_0(sK3,k5_xboole_0(sK3,k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)))) ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_4693,c_4693,c_10375]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2843,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1781,c_2236]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_3380,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_2677,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_6302,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_3380,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_8875,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
% 8.08/1.51      | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1246,c_1247]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_8881,plain,
% 8.08/1.51      ( k3_xboole_0(X0,k1_xboole_0) = X1
% 8.08/1.51      | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_8875,c_1644]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_14890,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),sK3),k3_subset_1(k2_struct_0(sK2),sK3)) = k3_xboole_0(X0,k1_xboole_0) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_8881,c_11142]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_14891,plain,
% 8.08/1.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_14890,c_11560]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_18535,plain,
% 8.08/1.51      ( k3_xboole_0(sK3,k3_xboole_0(sK3,k5_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)))) = k1_xboole_0 ),
% 8.08/1.51      inference(demodulation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_18534,c_2843,c_6302,c_12702,c_14891]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_3597,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_2843,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_18563,plain,
% 8.08/1.51      ( k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)) = k5_xboole_0(sK3,k1_xboole_0) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_18535,c_3597]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2323,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k3_xboole_0(X0,k3_xboole_0(X0,X0)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_2110,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2860,plain,
% 8.08/1.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0))) = k3_xboole_0(X0,k3_xboole_0(X0,X0)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_2323,c_2236]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_16016,plain,
% 8.08/1.51      ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,X0) ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_2860,c_1786,c_2860,c_14891]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2611,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)))) = k3_xboole_0(X0,k3_xboole_0(X0,X0)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_2531,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_16020,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)))) = k3_xboole_0(X0,X0) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_16016,c_2611]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_16022,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_16016,c_2531]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_16025,plain,
% 8.08/1.51      ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_16022,c_1644,c_14891]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_16027,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_16020,c_16025]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_16028,plain,
% 8.08/1.51      ( k3_xboole_0(X0,X0) = X0 ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_16027,c_13]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_16021,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k3_xboole_0(X0,X0) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_16016,c_2323]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_16026,plain,
% 8.08/1.51      ( k3_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_16021,c_14891]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_16029,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_16028,c_16026]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_17536,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),X0,k3_xboole_0(k2_struct_0(sK2),sK3)) = k3_xboole_0(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_17522,c_1235]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_17814,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),X0,k3_xboole_0(sK3,k2_struct_0(sK2))) = k3_xboole_0(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1781,c_17536]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_17526,plain,
% 8.08/1.51      ( m1_subset_1(k3_xboole_0(sK3,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1781,c_17522]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_17790,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),X0,k3_xboole_0(sK3,k2_struct_0(sK2))) = k3_xboole_0(X0,k3_xboole_0(sK3,k2_struct_0(sK2))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_17526,c_1235]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_17817,plain,
% 8.08/1.51      ( k3_xboole_0(X0,k3_xboole_0(sK3,k2_struct_0(sK2))) = k3_xboole_0(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_17814,c_17790]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_18566,plain,
% 8.08/1.51      ( k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)) = sK3 ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_18563,c_16029,c_17817]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_22547,plain,
% 8.08/1.51      ( r2_hidden(sK0(X0,sK3),k3_xboole_0(k2_struct_0(sK2),sK3)) != iProver_top
% 8.08/1.51      | r1_tarski(X0,sK3) = iProver_top ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_15711,c_18566]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_22551,plain,
% 8.08/1.51      ( r1_tarski(k3_xboole_0(k2_struct_0(sK2),sK3),sK3) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1250,c_22547]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_7921,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_subset_1(k2_struct_0(sK2),sK3)) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k2_struct_0(sK2)) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4006,c_1245]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_13270,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) = iProver_top
% 8.08/1.51      | r2_hidden(X0,k2_struct_0(sK2)) != iProver_top
% 8.08/1.51      | r2_hidden(X0,sK3) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_7921,c_4480]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_13289,plain,
% 8.08/1.51      ( r2_hidden(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) = iProver_top
% 8.08/1.51      | r2_hidden(X0,sK3) != iProver_top ),
% 8.08/1.51      inference(global_propositional_subsumption,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_13270,c_3711]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_13297,plain,
% 8.08/1.51      ( r2_hidden(sK0(X0,k3_xboole_0(k2_struct_0(sK2),sK3)),sK3) != iProver_top
% 8.08/1.51      | r1_tarski(X0,k3_xboole_0(k2_struct_0(sK2),sK3)) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_13289,c_1251]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_18527,plain,
% 8.08/1.51      ( r1_tarski(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1250,c_13297]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_18747,plain,
% 8.08/1.51      ( k3_xboole_0(k2_struct_0(sK2),sK3) = sK3
% 8.08/1.51      | r1_tarski(k3_xboole_0(k2_struct_0(sK2),sK3),sK3) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_18527,c_1242]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23250,plain,
% 8.08/1.51      ( k3_xboole_0(k2_struct_0(sK2),sK3) = sK3 ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_22551,c_18747]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4683,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3))))) = k3_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),sK3) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4598,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4697,plain,
% 8.08/1.51      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k3_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k5_xboole_0(k3_subset_1(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)),k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3))))) = k7_subset_1(k2_struct_0(sK2),sK3,k3_subset_1(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_4683,c_4598]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11971,plain,
% 8.08/1.51      ( k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k5_xboole_0(k3_xboole_0(k2_struct_0(sK2),sK3),k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3))))) = k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_4697,c_4697,c_10251,c_10375]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11980,plain,
% 8.08/1.51      ( k5_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k3_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k5_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k3_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2)))))) = k3_xboole_0(sK3,k3_xboole_0(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1781,c_11971]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_14867,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X0
% 8.08/1.51      | k3_xboole_0(X0,k1_xboole_0) = X0
% 8.08/1.51      | r2_hidden(sK1(X0,X0,X0),X0) = iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_8881,c_1247]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_15064,plain,
% 8.08/1.51      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0,X0,X0),X0) = iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_14867,c_1644,c_14891]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_11756,plain,
% 8.08/1.51      ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k3_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2))))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1781,c_11743]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_17095,plain,
% 8.08/1.51      ( k5_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k3_xboole_0(sK3,k3_xboole_0(sK3,k2_struct_0(sK2)))) = k1_xboole_0 ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_15064,c_11756]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23524,plain,
% 8.08/1.51      ( k5_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k3_xboole_0(k3_xboole_0(sK3,k2_struct_0(sK2)),k1_xboole_0)) = sK3 ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_11980,c_11980,c_17095,c_18566]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23525,plain,
% 8.08/1.51      ( k3_xboole_0(sK3,k2_struct_0(sK2)) = sK3 ),
% 8.08/1.51      inference(demodulation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_23524,c_13,c_14891,c_16029]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4003,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(sK3,k2_struct_0(sK2))) = k3_subset_1(k2_struct_0(sK2),sK3) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1781,c_3994]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23555,plain,
% 8.08/1.51      ( k3_subset_1(k2_struct_0(sK2),sK3) = k5_xboole_0(k2_struct_0(sK2),sK3) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_23525,c_4003]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23818,plain,
% 8.08/1.51      ( m1_subset_1(k5_xboole_0(k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 8.08/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_23555,c_1237]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_25430,plain,
% 8.08/1.51      ( m1_subset_1(k5_xboole_0(k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 8.08/1.51      inference(global_propositional_subsumption,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_23818,c_1252]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_25437,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3),X0) = k9_subset_1(k2_struct_0(sK2),X0,k5_xboole_0(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_25430,c_1240]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23706,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),X0,k5_xboole_0(k2_struct_0(sK2),sK3)) = k3_xboole_0(X0,k5_xboole_0(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_23555,c_9457]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_25456,plain,
% 8.08/1.51      ( k9_subset_1(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3),X0) = k3_xboole_0(X0,k5_xboole_0(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_25437,c_23706]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_25538,plain,
% 8.08/1.51      ( k3_xboole_0(k5_xboole_0(k2_struct_0(sK2),sK3),k2_struct_0(sK2)) = k3_xboole_0(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_25456,c_2620]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_6284,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(sK3,k2_struct_0(sK2))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_3994,c_3380]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_2680,plain,
% 8.08/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_1645,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_6918,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(sK3,k2_struct_0(sK2)))))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_6284,c_2680]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23550,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)))) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_23525,c_6918]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_6919,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(sK3,k2_struct_0(sK2))))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_6284,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23552,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_23525,c_6919]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23560,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3))) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_23552,c_23555]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_4132,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3))) = k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(superposition,[status(thm)],[c_4006,c_0]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23561,plain,
% 8.08/1.51      ( k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3))) = k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_23560,c_4132]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23564,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)))) = k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3))) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_23550,c_23555,c_23561]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23565,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)))) = k3_xboole_0(k2_struct_0(sK2),k3_subset_1(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_23564,c_23555,c_23561]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23566,plain,
% 8.08/1.51      ( k5_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),k3_xboole_0(k2_struct_0(sK2),sK3)))) = k3_xboole_0(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3)) ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_23565,c_23555]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23567,plain,
% 8.08/1.51      ( k3_xboole_0(k2_struct_0(sK2),k5_xboole_0(k2_struct_0(sK2),sK3)) = k5_xboole_0(k2_struct_0(sK2),sK3) ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_23566,c_23250]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_25540,plain,
% 8.08/1.51      ( k3_xboole_0(k5_xboole_0(k2_struct_0(sK2),sK3),k2_struct_0(sK2)) = k5_xboole_0(k2_struct_0(sK2),sK3) ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_25538,c_23567]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_33042,plain,
% 8.08/1.51      ( k7_subset_1(k2_struct_0(sK2),k2_struct_0(sK2),sK3) = k5_xboole_0(k2_struct_0(sK2),sK3) ),
% 8.08/1.51      inference(light_normalisation,
% 8.08/1.51                [status(thm)],
% 8.08/1.51                [c_33039,c_23250,c_23555,c_25540]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_30,negated_conjecture,
% 8.08/1.51      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | ~ v4_pre_topc(sK3,sK2) ),
% 8.08/1.51      inference(cnf_transformation,[],[f88]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_229,plain,
% 8.08/1.51      ( ~ v4_pre_topc(sK3,sK2)
% 8.08/1.51      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) ),
% 8.08/1.51      inference(prop_impl,[status(thm)],[c_30]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_230,plain,
% 8.08/1.51      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | ~ v4_pre_topc(sK3,sK2) ),
% 8.08/1.51      inference(renaming,[status(thm)],[c_229]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_27,plain,
% 8.08/1.51      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 8.08/1.51      | v4_pre_topc(X1,X0)
% 8.08/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.08/1.51      | ~ l1_pre_topc(X0) ),
% 8.08/1.51      inference(cnf_transformation,[],[f83]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_423,plain,
% 8.08/1.51      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 8.08/1.51      | v4_pre_topc(X1,X0)
% 8.08/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.08/1.51      | sK2 != X0 ),
% 8.08/1.51      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_424,plain,
% 8.08/1.51      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0),sK2)
% 8.08/1.51      | v4_pre_topc(X0,sK2)
% 8.08/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 8.08/1.51      inference(unflattening,[status(thm)],[c_423]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_463,plain,
% 8.08/1.51      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0),sK2)
% 8.08/1.51      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 8.08/1.51      | sK3 != X0
% 8.08/1.51      | sK2 != sK2 ),
% 8.08/1.51      inference(resolution_lifted,[status(thm)],[c_230,c_424]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_464,plain,
% 8.08/1.51      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 8.08/1.51      inference(unflattening,[status(thm)],[c_463]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_562,plain,
% 8.08/1.51      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) ),
% 8.08/1.51      inference(prop_impl,[status(thm)],[c_32,c_464]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_563,plain,
% 8.08/1.51      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) ),
% 8.08/1.51      inference(renaming,[status(thm)],[c_562]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1229,plain,
% 8.08/1.51      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) != iProver_top
% 8.08/1.51      | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) != iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1255,plain,
% 8.08/1.51      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) != iProver_top
% 8.08/1.51      | v3_pre_topc(k3_subset_1(k2_struct_0(sK2),sK3),sK2) != iProver_top ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_1229,c_404]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23728,plain,
% 8.08/1.51      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) != iProver_top
% 8.08/1.51      | v3_pre_topc(k5_xboole_0(k2_struct_0(sK2),sK3),sK2) != iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_23555,c_1255]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_33084,plain,
% 8.08/1.51      ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK2),sK3),sK2) != iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_33042,c_23728]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_31,negated_conjecture,
% 8.08/1.51      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | v4_pre_topc(sK3,sK2) ),
% 8.08/1.51      inference(cnf_transformation,[],[f87]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_231,plain,
% 8.08/1.51      ( v4_pre_topc(sK3,sK2)
% 8.08/1.51      | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) ),
% 8.08/1.51      inference(prop_impl,[status(thm)],[c_31]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_232,plain,
% 8.08/1.51      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | v4_pre_topc(sK3,sK2) ),
% 8.08/1.51      inference(renaming,[status(thm)],[c_231]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_28,plain,
% 8.08/1.51      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 8.08/1.51      | ~ v4_pre_topc(X1,X0)
% 8.08/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.08/1.51      | ~ l1_pre_topc(X0) ),
% 8.08/1.51      inference(cnf_transformation,[],[f82]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_408,plain,
% 8.08/1.51      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 8.08/1.51      | ~ v4_pre_topc(X1,X0)
% 8.08/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.08/1.51      | sK2 != X0 ),
% 8.08/1.51      inference(resolution_lifted,[status(thm)],[c_28,c_33]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_409,plain,
% 8.08/1.51      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0),sK2)
% 8.08/1.51      | ~ v4_pre_topc(X0,sK2)
% 8.08/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 8.08/1.51      inference(unflattening,[status(thm)],[c_408]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_449,plain,
% 8.08/1.51      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),X0),sK2)
% 8.08/1.51      | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 8.08/1.51      | sK3 != X0
% 8.08/1.51      | sK2 != sK2 ),
% 8.08/1.51      inference(resolution_lifted,[status(thm)],[c_232,c_409]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_450,plain,
% 8.08/1.51      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 8.08/1.51      inference(unflattening,[status(thm)],[c_449]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_564,plain,
% 8.08/1.51      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) ),
% 8.08/1.51      inference(prop_impl,[status(thm)],[c_32,c_450]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_565,plain,
% 8.08/1.51      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2)
% 8.08/1.51      | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) ),
% 8.08/1.51      inference(renaming,[status(thm)],[c_564]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1230,plain,
% 8.08/1.51      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) = iProver_top
% 8.08/1.51      | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),sK3),sK2) = iProver_top ),
% 8.08/1.51      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_1254,plain,
% 8.08/1.51      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) = iProver_top
% 8.08/1.51      | v3_pre_topc(k3_subset_1(k2_struct_0(sK2),sK3),sK2) = iProver_top ),
% 8.08/1.51      inference(light_normalisation,[status(thm)],[c_1230,c_404]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_23727,plain,
% 8.08/1.51      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK2),k2_struct_0(sK2),sK3),sK2) = iProver_top
% 8.08/1.51      | v3_pre_topc(k5_xboole_0(k2_struct_0(sK2),sK3),sK2) = iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_23555,c_1254]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(c_33083,plain,
% 8.08/1.51      ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK2),sK3),sK2) = iProver_top ),
% 8.08/1.51      inference(demodulation,[status(thm)],[c_33042,c_23727]) ).
% 8.08/1.51  
% 8.08/1.51  cnf(contradiction,plain,
% 8.08/1.51      ( $false ),
% 8.08/1.51      inference(minisat,[status(thm)],[c_33084,c_33083]) ).
% 8.08/1.51  
% 8.08/1.51  
% 8.08/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 8.08/1.51  
% 8.08/1.51  ------                               Statistics
% 8.08/1.51  
% 8.08/1.51  ------ General
% 8.08/1.51  
% 8.08/1.51  abstr_ref_over_cycles:                  0
% 8.08/1.51  abstr_ref_under_cycles:                 0
% 8.08/1.51  gc_basic_clause_elim:                   0
% 8.08/1.51  forced_gc_time:                         0
% 8.08/1.51  parsing_time:                           0.007
% 8.08/1.51  unif_index_cands_time:                  0.
% 8.08/1.51  unif_index_add_time:                    0.
% 8.08/1.51  orderings_time:                         0.
% 8.08/1.51  out_proof_time:                         0.021
% 8.08/1.51  total_time:                             0.991
% 8.08/1.51  num_of_symbols:                         54
% 8.08/1.51  num_of_terms:                           35355
% 8.08/1.51  
% 8.08/1.51  ------ Preprocessing
% 8.08/1.51  
% 8.08/1.51  num_of_splits:                          0
% 8.08/1.51  num_of_split_atoms:                     0
% 8.08/1.51  num_of_reused_defs:                     0
% 8.08/1.51  num_eq_ax_congr_red:                    45
% 8.08/1.51  num_of_sem_filtered_clauses:            1
% 8.08/1.51  num_of_subtypes:                        0
% 8.08/1.51  monotx_restored_types:                  0
% 8.08/1.51  sat_num_of_epr_types:                   0
% 8.08/1.51  sat_num_of_non_cyclic_types:            0
% 8.08/1.51  sat_guarded_non_collapsed_types:        0
% 8.08/1.51  num_pure_diseq_elim:                    0
% 8.08/1.51  simp_replaced_by:                       0
% 8.08/1.51  res_preprocessed:                       149
% 8.08/1.51  prep_upred:                             0
% 8.08/1.51  prep_unflattend:                        5
% 8.08/1.51  smt_new_axioms:                         0
% 8.08/1.51  pred_elim_cands:                        4
% 8.08/1.51  pred_elim:                              3
% 8.08/1.51  pred_elim_cl:                           4
% 8.08/1.51  pred_elim_cycles:                       5
% 8.08/1.51  merged_defs:                            8
% 8.08/1.51  merged_defs_ncl:                        0
% 8.08/1.51  bin_hyper_res:                          8
% 8.08/1.51  prep_cycles:                            4
% 8.08/1.51  pred_elim_time:                         0.001
% 8.08/1.51  splitting_time:                         0.
% 8.08/1.51  sem_filter_time:                        0.
% 8.08/1.51  monotx_time:                            0.
% 8.08/1.51  subtype_inf_time:                       0.
% 8.08/1.51  
% 8.08/1.51  ------ Problem properties
% 8.08/1.51  
% 8.08/1.51  clauses:                                29
% 8.08/1.51  conjectures:                            1
% 8.08/1.51  epr:                                    3
% 8.08/1.51  horn:                                   23
% 8.08/1.51  ground:                                 4
% 8.08/1.51  unary:                                  10
% 8.08/1.51  binary:                                 10
% 8.08/1.51  lits:                                   58
% 8.08/1.51  lits_eq:                                14
% 8.08/1.51  fd_pure:                                0
% 8.08/1.51  fd_pseudo:                              0
% 8.08/1.51  fd_cond:                                0
% 8.08/1.51  fd_pseudo_cond:                         4
% 8.08/1.51  ac_symbols:                             0
% 8.08/1.51  
% 8.08/1.51  ------ Propositional Solver
% 8.08/1.51  
% 8.08/1.51  prop_solver_calls:                      34
% 8.08/1.51  prop_fast_solver_calls:                 1648
% 8.08/1.51  smt_solver_calls:                       0
% 8.08/1.51  smt_fast_solver_calls:                  0
% 8.08/1.51  prop_num_of_clauses:                    12476
% 8.08/1.51  prop_preprocess_simplified:             23485
% 8.08/1.51  prop_fo_subsumed:                       34
% 8.08/1.51  prop_solver_time:                       0.
% 8.08/1.51  smt_solver_time:                        0.
% 8.08/1.51  smt_fast_solver_time:                   0.
% 8.08/1.51  prop_fast_solver_time:                  0.
% 8.08/1.51  prop_unsat_core_time:                   0.001
% 8.08/1.51  
% 8.08/1.51  ------ QBF
% 8.08/1.51  
% 8.08/1.51  qbf_q_res:                              0
% 8.08/1.51  qbf_num_tautologies:                    0
% 8.08/1.51  qbf_prep_cycles:                        0
% 8.08/1.51  
% 8.08/1.51  ------ BMC1
% 8.08/1.51  
% 8.08/1.51  bmc1_current_bound:                     -1
% 8.08/1.51  bmc1_last_solved_bound:                 -1
% 8.08/1.51  bmc1_unsat_core_size:                   -1
% 8.08/1.51  bmc1_unsat_core_parents_size:           -1
% 8.08/1.51  bmc1_merge_next_fun:                    0
% 8.08/1.51  bmc1_unsat_core_clauses_time:           0.
% 8.08/1.51  
% 8.08/1.51  ------ Instantiation
% 8.08/1.51  
% 8.08/1.51  inst_num_of_clauses:                    3685
% 8.08/1.51  inst_num_in_passive:                    1866
% 8.08/1.51  inst_num_in_active:                     1487
% 8.08/1.51  inst_num_in_unprocessed:                332
% 8.08/1.51  inst_num_of_loops:                      1880
% 8.08/1.51  inst_num_of_learning_restarts:          0
% 8.08/1.51  inst_num_moves_active_passive:          386
% 8.08/1.51  inst_lit_activity:                      0
% 8.08/1.51  inst_lit_activity_moves:                0
% 8.08/1.51  inst_num_tautologies:                   0
% 8.08/1.51  inst_num_prop_implied:                  0
% 8.08/1.51  inst_num_existing_simplified:           0
% 8.08/1.51  inst_num_eq_res_simplified:             0
% 8.08/1.51  inst_num_child_elim:                    0
% 8.08/1.51  inst_num_of_dismatching_blockings:      1840
% 8.08/1.51  inst_num_of_non_proper_insts:           4646
% 8.08/1.51  inst_num_of_duplicates:                 0
% 8.08/1.51  inst_inst_num_from_inst_to_res:         0
% 8.08/1.51  inst_dismatching_checking_time:         0.
% 8.08/1.51  
% 8.08/1.51  ------ Resolution
% 8.08/1.51  
% 8.08/1.51  res_num_of_clauses:                     0
% 8.08/1.51  res_num_in_passive:                     0
% 8.08/1.51  res_num_in_active:                      0
% 8.08/1.51  res_num_of_loops:                       153
% 8.08/1.51  res_forward_subset_subsumed:            269
% 8.08/1.51  res_backward_subset_subsumed:           0
% 8.08/1.51  res_forward_subsumed:                   0
% 8.08/1.51  res_backward_subsumed:                  0
% 8.08/1.51  res_forward_subsumption_resolution:     0
% 8.08/1.51  res_backward_subsumption_resolution:    0
% 8.08/1.51  res_clause_to_clause_subsumption:       13753
% 8.08/1.51  res_orphan_elimination:                 0
% 8.08/1.51  res_tautology_del:                      395
% 8.08/1.51  res_num_eq_res_simplified:              0
% 8.08/1.51  res_num_sel_changes:                    0
% 8.08/1.51  res_moves_from_active_to_pass:          0
% 8.08/1.51  
% 8.08/1.51  ------ Superposition
% 8.08/1.51  
% 8.08/1.51  sup_time_total:                         0.
% 8.08/1.51  sup_time_generating:                    0.
% 8.08/1.51  sup_time_sim_full:                      0.
% 8.08/1.51  sup_time_sim_immed:                     0.
% 8.08/1.51  
% 8.08/1.51  sup_num_of_clauses:                     1796
% 8.08/1.51  sup_num_in_active:                      214
% 8.08/1.51  sup_num_in_passive:                     1582
% 8.08/1.51  sup_num_of_loops:                       375
% 8.08/1.51  sup_fw_superposition:                   2503
% 8.08/1.51  sup_bw_superposition:                   1927
% 8.08/1.51  sup_immediate_simplified:               2032
% 8.08/1.51  sup_given_eliminated:                   10
% 8.08/1.51  comparisons_done:                       0
% 8.08/1.51  comparisons_avoided:                    33
% 8.08/1.51  
% 8.08/1.51  ------ Simplifications
% 8.08/1.51  
% 8.08/1.51  
% 8.08/1.51  sim_fw_subset_subsumed:                 57
% 8.08/1.51  sim_bw_subset_subsumed:                 17
% 8.08/1.51  sim_fw_subsumed:                        327
% 8.08/1.51  sim_bw_subsumed:                        33
% 8.08/1.51  sim_fw_subsumption_res:                 0
% 8.08/1.51  sim_bw_subsumption_res:                 0
% 8.08/1.51  sim_tautology_del:                      141
% 8.08/1.51  sim_eq_tautology_del:                   571
% 8.08/1.51  sim_eq_res_simp:                        4
% 8.08/1.51  sim_fw_demodulated:                     1031
% 8.08/1.51  sim_bw_demodulated:                     196
% 8.08/1.51  sim_light_normalised:                   1330
% 8.08/1.51  sim_joinable_taut:                      0
% 8.08/1.51  sim_joinable_simp:                      0
% 8.08/1.51  sim_ac_normalised:                      0
% 8.08/1.51  sim_smt_subsumption:                    0
% 8.08/1.51  
%------------------------------------------------------------------------------
