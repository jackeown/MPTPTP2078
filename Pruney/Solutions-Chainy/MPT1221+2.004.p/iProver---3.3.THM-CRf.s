%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:28 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :  141 (3413 expanded)
%              Number of clauses        :   81 (1113 expanded)
%              Number of leaves         :   17 ( 776 expanded)
%              Depth                    :   23
%              Number of atoms          :  410 (12229 expanded)
%              Number of equality atoms :  138 (1958 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f54,f45])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK2),X0)
          | ~ v4_pre_topc(sK2,X0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK2),X0)
          | v4_pre_topc(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X1),sK1)
            | ~ v4_pre_topc(X1,sK1) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X1),sK1)
            | v4_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
      | ~ v4_pre_topc(sK2,sK1) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
      | v4_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f45])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_938,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_950,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_938,c_15])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_939,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_951,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_939,c_15])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_928,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_16,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_286,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_19,c_16])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_300,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_286,c_23])).

cnf(c_301,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_941,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_928,c_301])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_934,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1353,plain,
    ( k3_subset_1(k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_941,c_934])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_932,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1477,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1353,c_932])).

cnf(c_1684,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1477,c_941])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_931,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1689,plain,
    ( r2_hidden(X0,k4_xboole_0(k2_struct_0(sK1),sK2)) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1684,c_931])).

cnf(c_3432,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(k2_struct_0(sK1),sK2))) = X1
    | r2_hidden(sK0(X0,k4_xboole_0(k2_struct_0(sK1),sK2),X1),X1) = iProver_top
    | r2_hidden(sK0(X0,k4_xboole_0(k2_struct_0(sK1),sK2),X1),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_1689])).

cnf(c_14474,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(k2_struct_0(sK1),sK2))) = k4_xboole_0(k2_struct_0(sK1),sK2)
    | r2_hidden(sK0(X0,k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3432,c_1689])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_940,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_952,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_940,c_15])).

cnf(c_14932,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2))) = k4_xboole_0(k2_struct_0(sK1),sK2)
    | r2_hidden(sK0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k4_xboole_0(k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14474,c_952])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_930,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_946,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_930,c_15])).

cnf(c_2194,plain,
    ( k9_subset_1(k2_struct_0(sK1),X0,k4_xboole_0(k2_struct_0(sK1),sK2)) = k1_setfam_1(k2_tarski(X0,k4_xboole_0(k2_struct_0(sK1),sK2))) ),
    inference(superposition,[status(thm)],[c_1684,c_946])).

cnf(c_10,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_933,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_942,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_933,c_8])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_929,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3464,plain,
    ( k9_subset_1(X0,X0,k3_subset_1(X0,X1)) = k7_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_942,c_929])).

cnf(c_9165,plain,
    ( k9_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK2)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_941,c_3464])).

cnf(c_9183,plain,
    ( k9_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) ),
    inference(light_normalisation,[status(thm)],[c_9165,c_1353])).

cnf(c_9190,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2))) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_2194,c_9183])).

cnf(c_14933,plain,
    ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2)
    | r2_hidden(sK0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k4_xboole_0(k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14932,c_9190])).

cnf(c_14984,plain,
    ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2)
    | k1_setfam_1(k2_tarski(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2))) = k4_xboole_0(k2_struct_0(sK1),sK2)
    | r2_hidden(sK0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_14933])).

cnf(c_14986,plain,
    ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2)
    | r2_hidden(sK0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14984,c_9190])).

cnf(c_14982,plain,
    ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2)
    | k1_setfam_1(k2_tarski(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2))) = k4_xboole_0(k2_struct_0(sK1),sK2)
    | r2_hidden(sK0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k4_xboole_0(k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_14933])).

cnf(c_14987,plain,
    ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2)
    | r2_hidden(sK0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k4_xboole_0(k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14982,c_9190])).

cnf(c_14991,plain,
    ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14986,c_14933,c_14987])).

cnf(c_20,negated_conjecture,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_163,plain,
    ( ~ v4_pre_topc(sK2,sK1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_164,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ v4_pre_topc(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_163])).

cnf(c_17,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_320,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_321,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_360,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_164,c_321])).

cnf(c_361,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_432,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) ),
    inference(prop_impl,[status(thm)],[c_22,c_361])).

cnf(c_433,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(renaming,[status(thm)],[c_432])).

cnf(c_926,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_948,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) != iProver_top
    | v3_pre_topc(k3_subset_1(k2_struct_0(sK1),sK2),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_926,c_301])).

cnf(c_1357,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) != iProver_top
    | v3_pre_topc(k4_xboole_0(k2_struct_0(sK1),sK2),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1353,c_948])).

cnf(c_15019,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK1),sK2),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14991,c_1357])).

cnf(c_21,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_165,plain,
    ( v4_pre_topc(sK2,sK1)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_166,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_18,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_305,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_306,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_346,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_166,c_306])).

cnf(c_347,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_434,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) ),
    inference(prop_impl,[status(thm)],[c_22,c_347])).

cnf(c_435,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(renaming,[status(thm)],[c_434])).

cnf(c_927,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) = iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_947,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) = iProver_top
    | v3_pre_topc(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_927,c_301])).

cnf(c_1356,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) = iProver_top
    | v3_pre_topc(k4_xboole_0(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1353,c_947])).

cnf(c_15018,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14991,c_1356])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15019,c_15018])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:56:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.64/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.64/1.49  
% 7.64/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.64/1.49  
% 7.64/1.49  ------  iProver source info
% 7.64/1.49  
% 7.64/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.64/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.64/1.49  git: non_committed_changes: false
% 7.64/1.49  git: last_make_outside_of_git: false
% 7.64/1.49  
% 7.64/1.49  ------ 
% 7.64/1.49  
% 7.64/1.49  ------ Input Options
% 7.64/1.49  
% 7.64/1.49  --out_options                           all
% 7.64/1.49  --tptp_safe_out                         true
% 7.64/1.49  --problem_path                          ""
% 7.64/1.49  --include_path                          ""
% 7.64/1.49  --clausifier                            res/vclausify_rel
% 7.64/1.49  --clausifier_options                    ""
% 7.64/1.49  --stdin                                 false
% 7.64/1.49  --stats_out                             all
% 7.64/1.49  
% 7.64/1.49  ------ General Options
% 7.64/1.49  
% 7.64/1.49  --fof                                   false
% 7.64/1.49  --time_out_real                         305.
% 7.64/1.49  --time_out_virtual                      -1.
% 7.64/1.49  --symbol_type_check                     false
% 7.64/1.49  --clausify_out                          false
% 7.64/1.49  --sig_cnt_out                           false
% 7.64/1.49  --trig_cnt_out                          false
% 7.64/1.49  --trig_cnt_out_tolerance                1.
% 7.64/1.49  --trig_cnt_out_sk_spl                   false
% 7.64/1.49  --abstr_cl_out                          false
% 7.64/1.49  
% 7.64/1.49  ------ Global Options
% 7.64/1.49  
% 7.64/1.49  --schedule                              default
% 7.64/1.49  --add_important_lit                     false
% 7.64/1.49  --prop_solver_per_cl                    1000
% 7.64/1.49  --min_unsat_core                        false
% 7.64/1.49  --soft_assumptions                      false
% 7.64/1.49  --soft_lemma_size                       3
% 7.64/1.49  --prop_impl_unit_size                   0
% 7.64/1.49  --prop_impl_unit                        []
% 7.64/1.49  --share_sel_clauses                     true
% 7.64/1.49  --reset_solvers                         false
% 7.64/1.49  --bc_imp_inh                            [conj_cone]
% 7.64/1.49  --conj_cone_tolerance                   3.
% 7.64/1.49  --extra_neg_conj                        none
% 7.64/1.49  --large_theory_mode                     true
% 7.64/1.49  --prolific_symb_bound                   200
% 7.64/1.49  --lt_threshold                          2000
% 7.64/1.49  --clause_weak_htbl                      true
% 7.64/1.49  --gc_record_bc_elim                     false
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing Options
% 7.64/1.49  
% 7.64/1.49  --preprocessing_flag                    true
% 7.64/1.49  --time_out_prep_mult                    0.1
% 7.64/1.49  --splitting_mode                        input
% 7.64/1.49  --splitting_grd                         true
% 7.64/1.49  --splitting_cvd                         false
% 7.64/1.49  --splitting_cvd_svl                     false
% 7.64/1.49  --splitting_nvd                         32
% 7.64/1.49  --sub_typing                            true
% 7.64/1.49  --prep_gs_sim                           true
% 7.64/1.49  --prep_unflatten                        true
% 7.64/1.49  --prep_res_sim                          true
% 7.64/1.49  --prep_upred                            true
% 7.64/1.49  --prep_sem_filter                       exhaustive
% 7.64/1.49  --prep_sem_filter_out                   false
% 7.64/1.49  --pred_elim                             true
% 7.64/1.49  --res_sim_input                         true
% 7.64/1.49  --eq_ax_congr_red                       true
% 7.64/1.49  --pure_diseq_elim                       true
% 7.64/1.49  --brand_transform                       false
% 7.64/1.49  --non_eq_to_eq                          false
% 7.64/1.49  --prep_def_merge                        true
% 7.64/1.49  --prep_def_merge_prop_impl              false
% 7.64/1.49  --prep_def_merge_mbd                    true
% 7.64/1.49  --prep_def_merge_tr_red                 false
% 7.64/1.49  --prep_def_merge_tr_cl                  false
% 7.64/1.49  --smt_preprocessing                     true
% 7.64/1.49  --smt_ac_axioms                         fast
% 7.64/1.49  --preprocessed_out                      false
% 7.64/1.49  --preprocessed_stats                    false
% 7.64/1.49  
% 7.64/1.49  ------ Abstraction refinement Options
% 7.64/1.49  
% 7.64/1.49  --abstr_ref                             []
% 7.64/1.49  --abstr_ref_prep                        false
% 7.64/1.49  --abstr_ref_until_sat                   false
% 7.64/1.49  --abstr_ref_sig_restrict                funpre
% 7.64/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.49  --abstr_ref_under                       []
% 7.64/1.49  
% 7.64/1.49  ------ SAT Options
% 7.64/1.49  
% 7.64/1.49  --sat_mode                              false
% 7.64/1.49  --sat_fm_restart_options                ""
% 7.64/1.49  --sat_gr_def                            false
% 7.64/1.49  --sat_epr_types                         true
% 7.64/1.49  --sat_non_cyclic_types                  false
% 7.64/1.49  --sat_finite_models                     false
% 7.64/1.49  --sat_fm_lemmas                         false
% 7.64/1.49  --sat_fm_prep                           false
% 7.64/1.49  --sat_fm_uc_incr                        true
% 7.64/1.49  --sat_out_model                         small
% 7.64/1.49  --sat_out_clauses                       false
% 7.64/1.49  
% 7.64/1.49  ------ QBF Options
% 7.64/1.49  
% 7.64/1.49  --qbf_mode                              false
% 7.64/1.49  --qbf_elim_univ                         false
% 7.64/1.49  --qbf_dom_inst                          none
% 7.64/1.49  --qbf_dom_pre_inst                      false
% 7.64/1.49  --qbf_sk_in                             false
% 7.64/1.49  --qbf_pred_elim                         true
% 7.64/1.49  --qbf_split                             512
% 7.64/1.49  
% 7.64/1.49  ------ BMC1 Options
% 7.64/1.49  
% 7.64/1.49  --bmc1_incremental                      false
% 7.64/1.49  --bmc1_axioms                           reachable_all
% 7.64/1.49  --bmc1_min_bound                        0
% 7.64/1.49  --bmc1_max_bound                        -1
% 7.64/1.49  --bmc1_max_bound_default                -1
% 7.64/1.49  --bmc1_symbol_reachability              true
% 7.64/1.49  --bmc1_property_lemmas                  false
% 7.64/1.49  --bmc1_k_induction                      false
% 7.64/1.49  --bmc1_non_equiv_states                 false
% 7.64/1.49  --bmc1_deadlock                         false
% 7.64/1.49  --bmc1_ucm                              false
% 7.64/1.49  --bmc1_add_unsat_core                   none
% 7.64/1.49  --bmc1_unsat_core_children              false
% 7.64/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.49  --bmc1_out_stat                         full
% 7.64/1.49  --bmc1_ground_init                      false
% 7.64/1.49  --bmc1_pre_inst_next_state              false
% 7.64/1.49  --bmc1_pre_inst_state                   false
% 7.64/1.49  --bmc1_pre_inst_reach_state             false
% 7.64/1.49  --bmc1_out_unsat_core                   false
% 7.64/1.49  --bmc1_aig_witness_out                  false
% 7.64/1.49  --bmc1_verbose                          false
% 7.64/1.49  --bmc1_dump_clauses_tptp                false
% 7.64/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.49  --bmc1_dump_file                        -
% 7.64/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.49  --bmc1_ucm_extend_mode                  1
% 7.64/1.49  --bmc1_ucm_init_mode                    2
% 7.64/1.49  --bmc1_ucm_cone_mode                    none
% 7.64/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.49  --bmc1_ucm_relax_model                  4
% 7.64/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.49  --bmc1_ucm_layered_model                none
% 7.64/1.49  --bmc1_ucm_max_lemma_size               10
% 7.64/1.49  
% 7.64/1.49  ------ AIG Options
% 7.64/1.49  
% 7.64/1.49  --aig_mode                              false
% 7.64/1.49  
% 7.64/1.49  ------ Instantiation Options
% 7.64/1.49  
% 7.64/1.49  --instantiation_flag                    true
% 7.64/1.49  --inst_sos_flag                         true
% 7.64/1.49  --inst_sos_phase                        true
% 7.64/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.49  --inst_lit_sel_side                     num_symb
% 7.64/1.49  --inst_solver_per_active                1400
% 7.64/1.49  --inst_solver_calls_frac                1.
% 7.64/1.49  --inst_passive_queue_type               priority_queues
% 7.64/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.49  --inst_passive_queues_freq              [25;2]
% 7.64/1.49  --inst_dismatching                      true
% 7.64/1.49  --inst_eager_unprocessed_to_passive     true
% 7.64/1.49  --inst_prop_sim_given                   true
% 7.64/1.49  --inst_prop_sim_new                     false
% 7.64/1.49  --inst_subs_new                         false
% 7.64/1.49  --inst_eq_res_simp                      false
% 7.64/1.49  --inst_subs_given                       false
% 7.64/1.49  --inst_orphan_elimination               true
% 7.64/1.49  --inst_learning_loop_flag               true
% 7.64/1.49  --inst_learning_start                   3000
% 7.64/1.49  --inst_learning_factor                  2
% 7.64/1.49  --inst_start_prop_sim_after_learn       3
% 7.64/1.49  --inst_sel_renew                        solver
% 7.64/1.49  --inst_lit_activity_flag                true
% 7.64/1.49  --inst_restr_to_given                   false
% 7.64/1.49  --inst_activity_threshold               500
% 7.64/1.49  --inst_out_proof                        true
% 7.64/1.49  
% 7.64/1.49  ------ Resolution Options
% 7.64/1.49  
% 7.64/1.49  --resolution_flag                       true
% 7.64/1.49  --res_lit_sel                           adaptive
% 7.64/1.49  --res_lit_sel_side                      none
% 7.64/1.49  --res_ordering                          kbo
% 7.64/1.49  --res_to_prop_solver                    active
% 7.64/1.49  --res_prop_simpl_new                    false
% 7.64/1.49  --res_prop_simpl_given                  true
% 7.64/1.49  --res_passive_queue_type                priority_queues
% 7.64/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.49  --res_passive_queues_freq               [15;5]
% 7.64/1.49  --res_forward_subs                      full
% 7.64/1.49  --res_backward_subs                     full
% 7.64/1.49  --res_forward_subs_resolution           true
% 7.64/1.49  --res_backward_subs_resolution          true
% 7.64/1.49  --res_orphan_elimination                true
% 7.64/1.49  --res_time_limit                        2.
% 7.64/1.49  --res_out_proof                         true
% 7.64/1.49  
% 7.64/1.49  ------ Superposition Options
% 7.64/1.49  
% 7.64/1.49  --superposition_flag                    true
% 7.64/1.49  --sup_passive_queue_type                priority_queues
% 7.64/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.64/1.49  --demod_completeness_check              fast
% 7.64/1.49  --demod_use_ground                      true
% 7.64/1.49  --sup_to_prop_solver                    passive
% 7.64/1.49  --sup_prop_simpl_new                    true
% 7.64/1.49  --sup_prop_simpl_given                  true
% 7.64/1.49  --sup_fun_splitting                     true
% 7.64/1.49  --sup_smt_interval                      50000
% 7.64/1.49  
% 7.64/1.49  ------ Superposition Simplification Setup
% 7.64/1.49  
% 7.64/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.64/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.64/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.64/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.64/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.64/1.49  --sup_immed_triv                        [TrivRules]
% 7.64/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.49  --sup_immed_bw_main                     []
% 7.64/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.64/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.49  --sup_input_bw                          []
% 7.64/1.49  
% 7.64/1.49  ------ Combination Options
% 7.64/1.49  
% 7.64/1.49  --comb_res_mult                         3
% 7.64/1.49  --comb_sup_mult                         2
% 7.64/1.49  --comb_inst_mult                        10
% 7.64/1.49  
% 7.64/1.49  ------ Debug Options
% 7.64/1.49  
% 7.64/1.49  --dbg_backtrace                         false
% 7.64/1.49  --dbg_dump_prop_clauses                 false
% 7.64/1.49  --dbg_dump_prop_clauses_file            -
% 7.64/1.49  --dbg_out_stat                          false
% 7.64/1.49  ------ Parsing...
% 7.64/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.64/1.49  ------ Proving...
% 7.64/1.49  ------ Problem Properties 
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  clauses                                 20
% 7.64/1.49  conjectures                             1
% 7.64/1.49  EPR                                     0
% 7.64/1.49  Horn                                    17
% 7.64/1.49  unary                                   7
% 7.64/1.49  binary                                  7
% 7.64/1.49  lits                                    40
% 7.64/1.49  lits eq                                 11
% 7.64/1.49  fd_pure                                 0
% 7.64/1.49  fd_pseudo                               0
% 7.64/1.49  fd_cond                                 0
% 7.64/1.49  fd_pseudo_cond                          3
% 7.64/1.49  AC symbols                              0
% 7.64/1.49  
% 7.64/1.49  ------ Schedule dynamic 5 is on 
% 7.64/1.49  
% 7.64/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  ------ 
% 7.64/1.49  Current options:
% 7.64/1.49  ------ 
% 7.64/1.49  
% 7.64/1.49  ------ Input Options
% 7.64/1.49  
% 7.64/1.49  --out_options                           all
% 7.64/1.49  --tptp_safe_out                         true
% 7.64/1.49  --problem_path                          ""
% 7.64/1.49  --include_path                          ""
% 7.64/1.49  --clausifier                            res/vclausify_rel
% 7.64/1.49  --clausifier_options                    ""
% 7.64/1.49  --stdin                                 false
% 7.64/1.49  --stats_out                             all
% 7.64/1.49  
% 7.64/1.49  ------ General Options
% 7.64/1.49  
% 7.64/1.49  --fof                                   false
% 7.64/1.49  --time_out_real                         305.
% 7.64/1.49  --time_out_virtual                      -1.
% 7.64/1.49  --symbol_type_check                     false
% 7.64/1.49  --clausify_out                          false
% 7.64/1.49  --sig_cnt_out                           false
% 7.64/1.49  --trig_cnt_out                          false
% 7.64/1.49  --trig_cnt_out_tolerance                1.
% 7.64/1.49  --trig_cnt_out_sk_spl                   false
% 7.64/1.49  --abstr_cl_out                          false
% 7.64/1.49  
% 7.64/1.49  ------ Global Options
% 7.64/1.49  
% 7.64/1.49  --schedule                              default
% 7.64/1.49  --add_important_lit                     false
% 7.64/1.49  --prop_solver_per_cl                    1000
% 7.64/1.49  --min_unsat_core                        false
% 7.64/1.49  --soft_assumptions                      false
% 7.64/1.49  --soft_lemma_size                       3
% 7.64/1.49  --prop_impl_unit_size                   0
% 7.64/1.49  --prop_impl_unit                        []
% 7.64/1.49  --share_sel_clauses                     true
% 7.64/1.49  --reset_solvers                         false
% 7.64/1.49  --bc_imp_inh                            [conj_cone]
% 7.64/1.49  --conj_cone_tolerance                   3.
% 7.64/1.49  --extra_neg_conj                        none
% 7.64/1.49  --large_theory_mode                     true
% 7.64/1.49  --prolific_symb_bound                   200
% 7.64/1.49  --lt_threshold                          2000
% 7.64/1.49  --clause_weak_htbl                      true
% 7.64/1.49  --gc_record_bc_elim                     false
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing Options
% 7.64/1.49  
% 7.64/1.49  --preprocessing_flag                    true
% 7.64/1.49  --time_out_prep_mult                    0.1
% 7.64/1.49  --splitting_mode                        input
% 7.64/1.49  --splitting_grd                         true
% 7.64/1.49  --splitting_cvd                         false
% 7.64/1.49  --splitting_cvd_svl                     false
% 7.64/1.49  --splitting_nvd                         32
% 7.64/1.49  --sub_typing                            true
% 7.64/1.49  --prep_gs_sim                           true
% 7.64/1.49  --prep_unflatten                        true
% 7.64/1.49  --prep_res_sim                          true
% 7.64/1.49  --prep_upred                            true
% 7.64/1.49  --prep_sem_filter                       exhaustive
% 7.64/1.49  --prep_sem_filter_out                   false
% 7.64/1.49  --pred_elim                             true
% 7.64/1.49  --res_sim_input                         true
% 7.64/1.49  --eq_ax_congr_red                       true
% 7.64/1.49  --pure_diseq_elim                       true
% 7.64/1.49  --brand_transform                       false
% 7.64/1.49  --non_eq_to_eq                          false
% 7.64/1.49  --prep_def_merge                        true
% 7.64/1.49  --prep_def_merge_prop_impl              false
% 7.64/1.49  --prep_def_merge_mbd                    true
% 7.64/1.49  --prep_def_merge_tr_red                 false
% 7.64/1.49  --prep_def_merge_tr_cl                  false
% 7.64/1.49  --smt_preprocessing                     true
% 7.64/1.49  --smt_ac_axioms                         fast
% 7.64/1.49  --preprocessed_out                      false
% 7.64/1.49  --preprocessed_stats                    false
% 7.64/1.49  
% 7.64/1.49  ------ Abstraction refinement Options
% 7.64/1.49  
% 7.64/1.49  --abstr_ref                             []
% 7.64/1.49  --abstr_ref_prep                        false
% 7.64/1.49  --abstr_ref_until_sat                   false
% 7.64/1.49  --abstr_ref_sig_restrict                funpre
% 7.64/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.49  --abstr_ref_under                       []
% 7.64/1.49  
% 7.64/1.49  ------ SAT Options
% 7.64/1.49  
% 7.64/1.49  --sat_mode                              false
% 7.64/1.49  --sat_fm_restart_options                ""
% 7.64/1.49  --sat_gr_def                            false
% 7.64/1.49  --sat_epr_types                         true
% 7.64/1.49  --sat_non_cyclic_types                  false
% 7.64/1.49  --sat_finite_models                     false
% 7.64/1.49  --sat_fm_lemmas                         false
% 7.64/1.49  --sat_fm_prep                           false
% 7.64/1.49  --sat_fm_uc_incr                        true
% 7.64/1.49  --sat_out_model                         small
% 7.64/1.49  --sat_out_clauses                       false
% 7.64/1.49  
% 7.64/1.49  ------ QBF Options
% 7.64/1.49  
% 7.64/1.49  --qbf_mode                              false
% 7.64/1.49  --qbf_elim_univ                         false
% 7.64/1.49  --qbf_dom_inst                          none
% 7.64/1.49  --qbf_dom_pre_inst                      false
% 7.64/1.49  --qbf_sk_in                             false
% 7.64/1.49  --qbf_pred_elim                         true
% 7.64/1.49  --qbf_split                             512
% 7.64/1.49  
% 7.64/1.49  ------ BMC1 Options
% 7.64/1.49  
% 7.64/1.49  --bmc1_incremental                      false
% 7.64/1.49  --bmc1_axioms                           reachable_all
% 7.64/1.49  --bmc1_min_bound                        0
% 7.64/1.49  --bmc1_max_bound                        -1
% 7.64/1.49  --bmc1_max_bound_default                -1
% 7.64/1.49  --bmc1_symbol_reachability              true
% 7.64/1.49  --bmc1_property_lemmas                  false
% 7.64/1.49  --bmc1_k_induction                      false
% 7.64/1.49  --bmc1_non_equiv_states                 false
% 7.64/1.49  --bmc1_deadlock                         false
% 7.64/1.49  --bmc1_ucm                              false
% 7.64/1.49  --bmc1_add_unsat_core                   none
% 7.64/1.49  --bmc1_unsat_core_children              false
% 7.64/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.49  --bmc1_out_stat                         full
% 7.64/1.49  --bmc1_ground_init                      false
% 7.64/1.49  --bmc1_pre_inst_next_state              false
% 7.64/1.49  --bmc1_pre_inst_state                   false
% 7.64/1.49  --bmc1_pre_inst_reach_state             false
% 7.64/1.49  --bmc1_out_unsat_core                   false
% 7.64/1.49  --bmc1_aig_witness_out                  false
% 7.64/1.49  --bmc1_verbose                          false
% 7.64/1.49  --bmc1_dump_clauses_tptp                false
% 7.64/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.49  --bmc1_dump_file                        -
% 7.64/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.49  --bmc1_ucm_extend_mode                  1
% 7.64/1.49  --bmc1_ucm_init_mode                    2
% 7.64/1.49  --bmc1_ucm_cone_mode                    none
% 7.64/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.49  --bmc1_ucm_relax_model                  4
% 7.64/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.49  --bmc1_ucm_layered_model                none
% 7.64/1.49  --bmc1_ucm_max_lemma_size               10
% 7.64/1.49  
% 7.64/1.49  ------ AIG Options
% 7.64/1.49  
% 7.64/1.49  --aig_mode                              false
% 7.64/1.49  
% 7.64/1.49  ------ Instantiation Options
% 7.64/1.49  
% 7.64/1.49  --instantiation_flag                    true
% 7.64/1.49  --inst_sos_flag                         true
% 7.64/1.49  --inst_sos_phase                        true
% 7.64/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.49  --inst_lit_sel_side                     none
% 7.64/1.49  --inst_solver_per_active                1400
% 7.64/1.49  --inst_solver_calls_frac                1.
% 7.64/1.49  --inst_passive_queue_type               priority_queues
% 7.64/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.49  --inst_passive_queues_freq              [25;2]
% 7.64/1.49  --inst_dismatching                      true
% 7.64/1.49  --inst_eager_unprocessed_to_passive     true
% 7.64/1.49  --inst_prop_sim_given                   true
% 7.64/1.49  --inst_prop_sim_new                     false
% 7.64/1.49  --inst_subs_new                         false
% 7.64/1.49  --inst_eq_res_simp                      false
% 7.64/1.49  --inst_subs_given                       false
% 7.64/1.49  --inst_orphan_elimination               true
% 7.64/1.49  --inst_learning_loop_flag               true
% 7.64/1.49  --inst_learning_start                   3000
% 7.64/1.49  --inst_learning_factor                  2
% 7.64/1.49  --inst_start_prop_sim_after_learn       3
% 7.64/1.49  --inst_sel_renew                        solver
% 7.64/1.49  --inst_lit_activity_flag                true
% 7.64/1.49  --inst_restr_to_given                   false
% 7.64/1.49  --inst_activity_threshold               500
% 7.64/1.49  --inst_out_proof                        true
% 7.64/1.49  
% 7.64/1.49  ------ Resolution Options
% 7.64/1.49  
% 7.64/1.49  --resolution_flag                       false
% 7.64/1.49  --res_lit_sel                           adaptive
% 7.64/1.49  --res_lit_sel_side                      none
% 7.64/1.49  --res_ordering                          kbo
% 7.64/1.49  --res_to_prop_solver                    active
% 7.64/1.49  --res_prop_simpl_new                    false
% 7.64/1.49  --res_prop_simpl_given                  true
% 7.64/1.49  --res_passive_queue_type                priority_queues
% 7.64/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.49  --res_passive_queues_freq               [15;5]
% 7.64/1.49  --res_forward_subs                      full
% 7.64/1.49  --res_backward_subs                     full
% 7.64/1.49  --res_forward_subs_resolution           true
% 7.64/1.49  --res_backward_subs_resolution          true
% 7.64/1.49  --res_orphan_elimination                true
% 7.64/1.49  --res_time_limit                        2.
% 7.64/1.49  --res_out_proof                         true
% 7.64/1.49  
% 7.64/1.49  ------ Superposition Options
% 7.64/1.49  
% 7.64/1.49  --superposition_flag                    true
% 7.64/1.49  --sup_passive_queue_type                priority_queues
% 7.64/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.64/1.49  --demod_completeness_check              fast
% 7.64/1.49  --demod_use_ground                      true
% 7.64/1.49  --sup_to_prop_solver                    passive
% 7.64/1.49  --sup_prop_simpl_new                    true
% 7.64/1.49  --sup_prop_simpl_given                  true
% 7.64/1.49  --sup_fun_splitting                     true
% 7.64/1.49  --sup_smt_interval                      50000
% 7.64/1.49  
% 7.64/1.49  ------ Superposition Simplification Setup
% 7.64/1.49  
% 7.64/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.64/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.64/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.64/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.64/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.64/1.49  --sup_immed_triv                        [TrivRules]
% 7.64/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.49  --sup_immed_bw_main                     []
% 7.64/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.64/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.49  --sup_input_bw                          []
% 7.64/1.49  
% 7.64/1.49  ------ Combination Options
% 7.64/1.49  
% 7.64/1.49  --comb_res_mult                         3
% 7.64/1.49  --comb_sup_mult                         2
% 7.64/1.49  --comb_inst_mult                        10
% 7.64/1.49  
% 7.64/1.49  ------ Debug Options
% 7.64/1.49  
% 7.64/1.49  --dbg_backtrace                         false
% 7.64/1.49  --dbg_dump_prop_clauses                 false
% 7.64/1.49  --dbg_dump_prop_clauses_file            -
% 7.64/1.49  --dbg_out_stat                          false
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  ------ Proving...
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  % SZS status Theorem for theBenchmark.p
% 7.64/1.49  
% 7.64/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.64/1.49  
% 7.64/1.49  fof(f1,axiom,(
% 7.64/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f27,plain,(
% 7.64/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.64/1.49    inference(nnf_transformation,[],[f1])).
% 7.64/1.49  
% 7.64/1.49  fof(f28,plain,(
% 7.64/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.64/1.49    inference(flattening,[],[f27])).
% 7.64/1.49  
% 7.64/1.49  fof(f29,plain,(
% 7.64/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.64/1.49    inference(rectify,[],[f28])).
% 7.64/1.49  
% 7.64/1.49  fof(f30,plain,(
% 7.64/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f31,plain,(
% 7.64/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.64/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 7.64/1.49  
% 7.64/1.49  fof(f41,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f31])).
% 7.64/1.49  
% 7.64/1.49  fof(f3,axiom,(
% 7.64/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f45,plain,(
% 7.64/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.64/1.49    inference(cnf_transformation,[],[f3])).
% 7.64/1.49  
% 7.64/1.49  fof(f66,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.64/1.49    inference(definition_unfolding,[],[f41,f45])).
% 7.64/1.49  
% 7.64/1.49  fof(f12,axiom,(
% 7.64/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f54,plain,(
% 7.64/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.64/1.49    inference(cnf_transformation,[],[f12])).
% 7.64/1.49  
% 7.64/1.49  fof(f71,plain,(
% 7.64/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.64/1.49    inference(definition_unfolding,[],[f54,f45])).
% 7.64/1.49  
% 7.64/1.49  fof(f42,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f31])).
% 7.64/1.49  
% 7.64/1.49  fof(f65,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.64/1.49    inference(definition_unfolding,[],[f42,f45])).
% 7.64/1.49  
% 7.64/1.49  fof(f16,conjecture,(
% 7.64/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f17,negated_conjecture,(
% 7.64/1.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.64/1.49    inference(negated_conjecture,[],[f16])).
% 7.64/1.49  
% 7.64/1.49  fof(f26,plain,(
% 7.64/1.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.64/1.49    inference(ennf_transformation,[],[f17])).
% 7.64/1.49  
% 7.64/1.49  fof(f33,plain,(
% 7.64/1.49    ? [X0] : (? [X1] : (((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.64/1.49    inference(nnf_transformation,[],[f26])).
% 7.64/1.49  
% 7.64/1.49  fof(f34,plain,(
% 7.64/1.49    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.64/1.49    inference(flattening,[],[f33])).
% 7.64/1.49  
% 7.64/1.49  fof(f36,plain,(
% 7.64/1.49    ( ! [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK2),X0) | ~v4_pre_topc(sK2,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK2),X0) | v4_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f35,plain,(
% 7.64/1.49    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X1),sK1) | ~v4_pre_topc(X1,sK1)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X1),sK1) | v4_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 7.64/1.49    introduced(choice_axiom,[])).
% 7.64/1.49  
% 7.64/1.49  fof(f37,plain,(
% 7.64/1.49    ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) | ~v4_pre_topc(sK2,sK1)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) | v4_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 7.64/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).
% 7.64/1.49  
% 7.64/1.49  fof(f60,plain,(
% 7.64/1.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.64/1.49    inference(cnf_transformation,[],[f37])).
% 7.64/1.49  
% 7.64/1.49  fof(f15,axiom,(
% 7.64/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f25,plain,(
% 7.64/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.64/1.49    inference(ennf_transformation,[],[f15])).
% 7.64/1.49  
% 7.64/1.49  fof(f58,plain,(
% 7.64/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f25])).
% 7.64/1.49  
% 7.64/1.49  fof(f13,axiom,(
% 7.64/1.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f23,plain,(
% 7.64/1.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.64/1.49    inference(ennf_transformation,[],[f13])).
% 7.64/1.49  
% 7.64/1.49  fof(f55,plain,(
% 7.64/1.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f23])).
% 7.64/1.49  
% 7.64/1.49  fof(f59,plain,(
% 7.64/1.49    l1_pre_topc(sK1)),
% 7.64/1.49    inference(cnf_transformation,[],[f37])).
% 7.64/1.49  
% 7.64/1.49  fof(f6,axiom,(
% 7.64/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f18,plain,(
% 7.64/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.64/1.49    inference(ennf_transformation,[],[f6])).
% 7.64/1.49  
% 7.64/1.49  fof(f48,plain,(
% 7.64/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.64/1.49    inference(cnf_transformation,[],[f18])).
% 7.64/1.49  
% 7.64/1.49  fof(f8,axiom,(
% 7.64/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f19,plain,(
% 7.64/1.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.64/1.49    inference(ennf_transformation,[],[f8])).
% 7.64/1.49  
% 7.64/1.49  fof(f50,plain,(
% 7.64/1.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.64/1.49    inference(cnf_transformation,[],[f19])).
% 7.64/1.49  
% 7.64/1.49  fof(f9,axiom,(
% 7.64/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f20,plain,(
% 7.64/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.64/1.49    inference(ennf_transformation,[],[f9])).
% 7.64/1.49  
% 7.64/1.49  fof(f51,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.64/1.49    inference(cnf_transformation,[],[f20])).
% 7.64/1.49  
% 7.64/1.49  fof(f43,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f31])).
% 7.64/1.49  
% 7.64/1.49  fof(f64,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.64/1.49    inference(definition_unfolding,[],[f43,f45])).
% 7.64/1.49  
% 7.64/1.49  fof(f10,axiom,(
% 7.64/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f21,plain,(
% 7.64/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.64/1.49    inference(ennf_transformation,[],[f10])).
% 7.64/1.49  
% 7.64/1.49  fof(f52,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.64/1.49    inference(cnf_transformation,[],[f21])).
% 7.64/1.49  
% 7.64/1.49  fof(f70,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.64/1.49    inference(definition_unfolding,[],[f52,f45])).
% 7.64/1.49  
% 7.64/1.49  fof(f7,axiom,(
% 7.64/1.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f49,plain,(
% 7.64/1.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.64/1.49    inference(cnf_transformation,[],[f7])).
% 7.64/1.49  
% 7.64/1.49  fof(f5,axiom,(
% 7.64/1.49    ! [X0] : k2_subset_1(X0) = X0),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f47,plain,(
% 7.64/1.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.64/1.49    inference(cnf_transformation,[],[f5])).
% 7.64/1.49  
% 7.64/1.49  fof(f11,axiom,(
% 7.64/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f22,plain,(
% 7.64/1.49    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.64/1.49    inference(ennf_transformation,[],[f11])).
% 7.64/1.49  
% 7.64/1.49  fof(f53,plain,(
% 7.64/1.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.64/1.49    inference(cnf_transformation,[],[f22])).
% 7.64/1.49  
% 7.64/1.49  fof(f62,plain,(
% 7.64/1.49    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) | ~v4_pre_topc(sK2,sK1)),
% 7.64/1.49    inference(cnf_transformation,[],[f37])).
% 7.64/1.49  
% 7.64/1.49  fof(f14,axiom,(
% 7.64/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 7.64/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.49  
% 7.64/1.49  fof(f24,plain,(
% 7.64/1.49    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.64/1.49    inference(ennf_transformation,[],[f14])).
% 7.64/1.49  
% 7.64/1.49  fof(f32,plain,(
% 7.64/1.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.64/1.49    inference(nnf_transformation,[],[f24])).
% 7.64/1.49  
% 7.64/1.49  fof(f57,plain,(
% 7.64/1.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f32])).
% 7.64/1.49  
% 7.64/1.49  fof(f61,plain,(
% 7.64/1.49    v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) | v4_pre_topc(sK2,sK1)),
% 7.64/1.49    inference(cnf_transformation,[],[f37])).
% 7.64/1.49  
% 7.64/1.49  fof(f56,plain,(
% 7.64/1.49    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.64/1.49    inference(cnf_transformation,[],[f32])).
% 7.64/1.49  
% 7.64/1.49  cnf(c_3,plain,
% 7.64/1.49      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.64/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 7.64/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_938,plain,
% 7.64/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_15,plain,
% 7.64/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 7.64/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_950,plain,
% 7.64/1.49      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_938,c_15]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2,plain,
% 7.64/1.49      ( r2_hidden(sK0(X0,X1,X2),X1)
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.64/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 7.64/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_939,plain,
% 7.64/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_951,plain,
% 7.64/1.49      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_939,c_15]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_22,negated_conjecture,
% 7.64/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.64/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_928,plain,
% 7.64/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_19,plain,
% 7.64/1.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_16,plain,
% 7.64/1.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_286,plain,
% 7.64/1.49      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.64/1.49      inference(resolution,[status(thm)],[c_19,c_16]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_23,negated_conjecture,
% 7.64/1.49      ( l1_pre_topc(sK1) ),
% 7.64/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_300,plain,
% 7.64/1.49      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 7.64/1.49      inference(resolution_lifted,[status(thm)],[c_286,c_23]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_301,plain,
% 7.64/1.49      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 7.64/1.49      inference(unflattening,[status(thm)],[c_300]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_941,plain,
% 7.64/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 7.64/1.49      inference(light_normalisation,[status(thm)],[c_928,c_301]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_9,plain,
% 7.64/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.64/1.49      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_934,plain,
% 7.64/1.49      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.64/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1353,plain,
% 7.64/1.49      ( k3_subset_1(k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2) ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_941,c_934]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_11,plain,
% 7.64/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.64/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.64/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_932,plain,
% 7.64/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.64/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1477,plain,
% 7.64/1.49      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 7.64/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1353,c_932]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1684,plain,
% 7.64/1.49      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 7.64/1.49      inference(global_propositional_subsumption,
% 7.64/1.49                [status(thm)],
% 7.64/1.49                [c_1477,c_941]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_12,plain,
% 7.64/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.64/1.49      | ~ r2_hidden(X2,X0)
% 7.64/1.49      | r2_hidden(X2,X1) ),
% 7.64/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_931,plain,
% 7.64/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.64/1.49      | r2_hidden(X2,X0) != iProver_top
% 7.64/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1689,plain,
% 7.64/1.49      ( r2_hidden(X0,k4_xboole_0(k2_struct_0(sK1),sK2)) != iProver_top
% 7.64/1.49      | r2_hidden(X0,k2_struct_0(sK1)) = iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1684,c_931]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_3432,plain,
% 7.64/1.49      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(k2_struct_0(sK1),sK2))) = X1
% 7.64/1.49      | r2_hidden(sK0(X0,k4_xboole_0(k2_struct_0(sK1),sK2),X1),X1) = iProver_top
% 7.64/1.49      | r2_hidden(sK0(X0,k4_xboole_0(k2_struct_0(sK1),sK2),X1),k2_struct_0(sK1)) = iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_951,c_1689]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_14474,plain,
% 7.64/1.49      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(k2_struct_0(sK1),sK2))) = k4_xboole_0(k2_struct_0(sK1),sK2)
% 7.64/1.49      | r2_hidden(sK0(X0,k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k2_struct_0(sK1)) = iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_3432,c_1689]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1,plain,
% 7.64/1.49      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.64/1.49      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.64/1.49      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.64/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 7.64/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_940,plain,
% 7.64/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_952,plain,
% 7.64/1.49      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 7.64/1.49      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_940,c_15]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_14932,plain,
% 7.64/1.49      ( k1_setfam_1(k2_tarski(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2))) = k4_xboole_0(k2_struct_0(sK1),sK2)
% 7.64/1.49      | r2_hidden(sK0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k4_xboole_0(k2_struct_0(sK1),sK2)) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_14474,c_952]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_13,plain,
% 7.64/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.64/1.49      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_930,plain,
% 7.64/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 7.64/1.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_946,plain,
% 7.64/1.49      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 7.64/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.64/1.49      inference(light_normalisation,[status(thm)],[c_930,c_15]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_2194,plain,
% 7.64/1.49      ( k9_subset_1(k2_struct_0(sK1),X0,k4_xboole_0(k2_struct_0(sK1),sK2)) = k1_setfam_1(k2_tarski(X0,k4_xboole_0(k2_struct_0(sK1),sK2))) ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_1684,c_946]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_10,plain,
% 7.64/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 7.64/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_933,plain,
% 7.64/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_8,plain,
% 7.64/1.49      ( k2_subset_1(X0) = X0 ),
% 7.64/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_942,plain,
% 7.64/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.64/1.49      inference(light_normalisation,[status(thm)],[c_933,c_8]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_14,plain,
% 7.64/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.64/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.64/1.49      | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
% 7.64/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_929,plain,
% 7.64/1.49      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 7.64/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.64/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_3464,plain,
% 7.64/1.49      ( k9_subset_1(X0,X0,k3_subset_1(X0,X1)) = k7_subset_1(X0,X0,X1)
% 7.64/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_942,c_929]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_9165,plain,
% 7.64/1.49      ( k9_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK2)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_941,c_3464]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_9183,plain,
% 7.64/1.49      ( k9_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) ),
% 7.64/1.49      inference(light_normalisation,[status(thm)],[c_9165,c_1353]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_9190,plain,
% 7.64/1.49      ( k1_setfam_1(k2_tarski(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2))) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_2194,c_9183]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_14933,plain,
% 7.64/1.49      ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2)
% 7.64/1.49      | r2_hidden(sK0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k4_xboole_0(k2_struct_0(sK1),sK2)) != iProver_top ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_14932,c_9190]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_14984,plain,
% 7.64/1.49      ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2)
% 7.64/1.49      | k1_setfam_1(k2_tarski(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2))) = k4_xboole_0(k2_struct_0(sK1),sK2)
% 7.64/1.49      | r2_hidden(sK0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k2_struct_0(sK1)) = iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_950,c_14933]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_14986,plain,
% 7.64/1.49      ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2)
% 7.64/1.49      | r2_hidden(sK0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k2_struct_0(sK1)) = iProver_top ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_14984,c_9190]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_14982,plain,
% 7.64/1.49      ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2)
% 7.64/1.49      | k1_setfam_1(k2_tarski(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2))) = k4_xboole_0(k2_struct_0(sK1),sK2)
% 7.64/1.49      | r2_hidden(sK0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k4_xboole_0(k2_struct_0(sK1),sK2)) = iProver_top ),
% 7.64/1.49      inference(superposition,[status(thm)],[c_951,c_14933]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_14987,plain,
% 7.64/1.49      ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2)
% 7.64/1.49      | r2_hidden(sK0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),sK2),k4_xboole_0(k2_struct_0(sK1),sK2)),k4_xboole_0(k2_struct_0(sK1),sK2)) = iProver_top ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_14982,c_9190]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_14991,plain,
% 7.64/1.49      ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k4_xboole_0(k2_struct_0(sK1),sK2) ),
% 7.64/1.49      inference(global_propositional_subsumption,
% 7.64/1.49                [status(thm)],
% 7.64/1.49                [c_14986,c_14933,c_14987]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_20,negated_conjecture,
% 7.64/1.49      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | ~ v4_pre_topc(sK2,sK1) ),
% 7.64/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_163,plain,
% 7.64/1.49      ( ~ v4_pre_topc(sK2,sK1)
% 7.64/1.49      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
% 7.64/1.49      inference(prop_impl,[status(thm)],[c_20]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_164,plain,
% 7.64/1.49      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | ~ v4_pre_topc(sK2,sK1) ),
% 7.64/1.49      inference(renaming,[status(thm)],[c_163]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_17,plain,
% 7.64/1.49      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 7.64/1.49      | v4_pre_topc(X1,X0)
% 7.64/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.64/1.49      | ~ l1_pre_topc(X0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_320,plain,
% 7.64/1.49      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 7.64/1.49      | v4_pre_topc(X1,X0)
% 7.64/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.64/1.49      | sK1 != X0 ),
% 7.64/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_321,plain,
% 7.64/1.49      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
% 7.64/1.49      | v4_pre_topc(X0,sK1)
% 7.64/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.64/1.49      inference(unflattening,[status(thm)],[c_320]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_360,plain,
% 7.64/1.49      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
% 7.64/1.49      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.64/1.49      | sK2 != X0
% 7.64/1.49      | sK1 != sK1 ),
% 7.64/1.49      inference(resolution_lifted,[status(thm)],[c_164,c_321]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_361,plain,
% 7.64/1.49      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.64/1.49      inference(unflattening,[status(thm)],[c_360]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_432,plain,
% 7.64/1.49      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) ),
% 7.64/1.49      inference(prop_impl,[status(thm)],[c_22,c_361]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_433,plain,
% 7.64/1.49      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
% 7.64/1.49      inference(renaming,[status(thm)],[c_432]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_926,plain,
% 7.64/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) != iProver_top
% 7.64/1.49      | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) != iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_948,plain,
% 7.64/1.49      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) != iProver_top
% 7.64/1.49      | v3_pre_topc(k3_subset_1(k2_struct_0(sK1),sK2),sK1) != iProver_top ),
% 7.64/1.49      inference(light_normalisation,[status(thm)],[c_926,c_301]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1357,plain,
% 7.64/1.49      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) != iProver_top
% 7.64/1.49      | v3_pre_topc(k4_xboole_0(k2_struct_0(sK1),sK2),sK1) != iProver_top ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_1353,c_948]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_15019,plain,
% 7.64/1.49      ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK1),sK2),sK1) != iProver_top ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_14991,c_1357]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_21,negated_conjecture,
% 7.64/1.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | v4_pre_topc(sK2,sK1) ),
% 7.64/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_165,plain,
% 7.64/1.49      ( v4_pre_topc(sK2,sK1)
% 7.64/1.49      | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
% 7.64/1.49      inference(prop_impl,[status(thm)],[c_21]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_166,plain,
% 7.64/1.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | v4_pre_topc(sK2,sK1) ),
% 7.64/1.49      inference(renaming,[status(thm)],[c_165]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_18,plain,
% 7.64/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 7.64/1.49      | ~ v4_pre_topc(X1,X0)
% 7.64/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.64/1.49      | ~ l1_pre_topc(X0) ),
% 7.64/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_305,plain,
% 7.64/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 7.64/1.49      | ~ v4_pre_topc(X1,X0)
% 7.64/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.64/1.49      | sK1 != X0 ),
% 7.64/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_306,plain,
% 7.64/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
% 7.64/1.49      | ~ v4_pre_topc(X0,sK1)
% 7.64/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.64/1.49      inference(unflattening,[status(thm)],[c_305]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_346,plain,
% 7.64/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
% 7.64/1.49      | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.64/1.49      | sK2 != X0
% 7.64/1.49      | sK1 != sK1 ),
% 7.64/1.49      inference(resolution_lifted,[status(thm)],[c_166,c_306]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_347,plain,
% 7.64/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.64/1.49      inference(unflattening,[status(thm)],[c_346]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_434,plain,
% 7.64/1.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) ),
% 7.64/1.49      inference(prop_impl,[status(thm)],[c_22,c_347]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_435,plain,
% 7.64/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
% 7.64/1.49      | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
% 7.64/1.49      inference(renaming,[status(thm)],[c_434]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_927,plain,
% 7.64/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) = iProver_top
% 7.64/1.49      | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top ),
% 7.64/1.49      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_947,plain,
% 7.64/1.49      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) = iProver_top
% 7.64/1.49      | v3_pre_topc(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
% 7.64/1.49      inference(light_normalisation,[status(thm)],[c_927,c_301]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_1356,plain,
% 7.64/1.49      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) = iProver_top
% 7.64/1.49      | v3_pre_topc(k4_xboole_0(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_1353,c_947]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(c_15018,plain,
% 7.64/1.49      ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
% 7.64/1.49      inference(demodulation,[status(thm)],[c_14991,c_1356]) ).
% 7.64/1.49  
% 7.64/1.49  cnf(contradiction,plain,
% 7.64/1.49      ( $false ),
% 7.64/1.49      inference(minisat,[status(thm)],[c_15019,c_15018]) ).
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.64/1.49  
% 7.64/1.49  ------                               Statistics
% 7.64/1.49  
% 7.64/1.49  ------ General
% 7.64/1.49  
% 7.64/1.49  abstr_ref_over_cycles:                  0
% 7.64/1.49  abstr_ref_under_cycles:                 0
% 7.64/1.49  gc_basic_clause_elim:                   0
% 7.64/1.49  forced_gc_time:                         0
% 7.64/1.49  parsing_time:                           0.009
% 7.64/1.49  unif_index_cands_time:                  0.
% 7.64/1.49  unif_index_add_time:                    0.
% 7.64/1.49  orderings_time:                         0.
% 7.64/1.49  out_proof_time:                         0.01
% 7.64/1.49  total_time:                             0.6
% 7.64/1.49  num_of_symbols:                         51
% 7.64/1.49  num_of_terms:                           19929
% 7.64/1.49  
% 7.64/1.49  ------ Preprocessing
% 7.64/1.49  
% 7.64/1.49  num_of_splits:                          0
% 7.64/1.49  num_of_split_atoms:                     0
% 7.64/1.49  num_of_reused_defs:                     0
% 7.64/1.49  num_eq_ax_congr_red:                    33
% 7.64/1.49  num_of_sem_filtered_clauses:            1
% 7.64/1.49  num_of_subtypes:                        0
% 7.64/1.49  monotx_restored_types:                  0
% 7.64/1.49  sat_num_of_epr_types:                   0
% 7.64/1.49  sat_num_of_non_cyclic_types:            0
% 7.64/1.49  sat_guarded_non_collapsed_types:        0
% 7.64/1.49  num_pure_diseq_elim:                    0
% 7.64/1.49  simp_replaced_by:                       0
% 7.64/1.49  res_preprocessed:                       113
% 7.64/1.49  prep_upred:                             0
% 7.64/1.49  prep_unflattend:                        5
% 7.64/1.49  smt_new_axioms:                         0
% 7.64/1.49  pred_elim_cands:                        3
% 7.64/1.49  pred_elim:                              3
% 7.64/1.49  pred_elim_cl:                           4
% 7.64/1.49  pred_elim_cycles:                       5
% 7.64/1.49  merged_defs:                            8
% 7.64/1.49  merged_defs_ncl:                        0
% 7.64/1.49  bin_hyper_res:                          8
% 7.64/1.49  prep_cycles:                            4
% 7.64/1.49  pred_elim_time:                         0.002
% 7.64/1.49  splitting_time:                         0.
% 7.64/1.49  sem_filter_time:                        0.
% 7.64/1.49  monotx_time:                            0.001
% 7.64/1.49  subtype_inf_time:                       0.
% 7.64/1.49  
% 7.64/1.49  ------ Problem properties
% 7.64/1.49  
% 7.64/1.49  clauses:                                20
% 7.64/1.49  conjectures:                            1
% 7.64/1.49  epr:                                    0
% 7.64/1.49  horn:                                   17
% 7.64/1.49  ground:                                 4
% 7.64/1.49  unary:                                  7
% 7.64/1.49  binary:                                 7
% 7.64/1.49  lits:                                   40
% 7.64/1.49  lits_eq:                                11
% 7.64/1.49  fd_pure:                                0
% 7.64/1.49  fd_pseudo:                              0
% 7.64/1.49  fd_cond:                                0
% 7.64/1.49  fd_pseudo_cond:                         3
% 7.64/1.49  ac_symbols:                             0
% 7.64/1.49  
% 7.64/1.49  ------ Propositional Solver
% 7.64/1.49  
% 7.64/1.49  prop_solver_calls:                      36
% 7.64/1.49  prop_fast_solver_calls:                 816
% 7.64/1.49  smt_solver_calls:                       0
% 7.64/1.49  smt_fast_solver_calls:                  0
% 7.64/1.49  prop_num_of_clauses:                    6142
% 7.64/1.49  prop_preprocess_simplified:             13171
% 7.64/1.49  prop_fo_subsumed:                       9
% 7.64/1.49  prop_solver_time:                       0.
% 7.64/1.49  smt_solver_time:                        0.
% 7.64/1.49  smt_fast_solver_time:                   0.
% 7.64/1.49  prop_fast_solver_time:                  0.
% 7.64/1.49  prop_unsat_core_time:                   0.
% 7.64/1.49  
% 7.64/1.49  ------ QBF
% 7.64/1.49  
% 7.64/1.49  qbf_q_res:                              0
% 7.64/1.49  qbf_num_tautologies:                    0
% 7.64/1.49  qbf_prep_cycles:                        0
% 7.64/1.49  
% 7.64/1.49  ------ BMC1
% 7.64/1.49  
% 7.64/1.49  bmc1_current_bound:                     -1
% 7.64/1.49  bmc1_last_solved_bound:                 -1
% 7.64/1.49  bmc1_unsat_core_size:                   -1
% 7.64/1.49  bmc1_unsat_core_parents_size:           -1
% 7.64/1.49  bmc1_merge_next_fun:                    0
% 7.64/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.64/1.49  
% 7.64/1.49  ------ Instantiation
% 7.64/1.49  
% 7.64/1.49  inst_num_of_clauses:                    2425
% 7.64/1.49  inst_num_in_passive:                    1498
% 7.64/1.49  inst_num_in_active:                     864
% 7.64/1.49  inst_num_in_unprocessed:                63
% 7.64/1.49  inst_num_of_loops:                      1010
% 7.64/1.49  inst_num_of_learning_restarts:          0
% 7.64/1.49  inst_num_moves_active_passive:          138
% 7.64/1.49  inst_lit_activity:                      0
% 7.64/1.49  inst_lit_activity_moves:                0
% 7.64/1.49  inst_num_tautologies:                   0
% 7.64/1.49  inst_num_prop_implied:                  0
% 7.64/1.49  inst_num_existing_simplified:           0
% 7.64/1.49  inst_num_eq_res_simplified:             0
% 7.64/1.49  inst_num_child_elim:                    0
% 7.64/1.49  inst_num_of_dismatching_blockings:      523
% 7.64/1.49  inst_num_of_non_proper_insts:           2258
% 7.64/1.49  inst_num_of_duplicates:                 0
% 7.64/1.49  inst_inst_num_from_inst_to_res:         0
% 7.64/1.49  inst_dismatching_checking_time:         0.
% 7.64/1.49  
% 7.64/1.49  ------ Resolution
% 7.64/1.49  
% 7.64/1.49  res_num_of_clauses:                     0
% 7.64/1.49  res_num_in_passive:                     0
% 7.64/1.49  res_num_in_active:                      0
% 7.64/1.49  res_num_of_loops:                       117
% 7.64/1.49  res_forward_subset_subsumed:            338
% 7.64/1.49  res_backward_subset_subsumed:           0
% 7.64/1.49  res_forward_subsumed:                   0
% 7.64/1.49  res_backward_subsumed:                  0
% 7.64/1.49  res_forward_subsumption_resolution:     0
% 7.64/1.49  res_backward_subsumption_resolution:    0
% 7.64/1.49  res_clause_to_clause_subsumption:       6126
% 7.64/1.49  res_orphan_elimination:                 0
% 7.64/1.49  res_tautology_del:                      172
% 7.64/1.49  res_num_eq_res_simplified:              0
% 7.64/1.49  res_num_sel_changes:                    0
% 7.64/1.49  res_moves_from_active_to_pass:          0
% 7.64/1.49  
% 7.64/1.49  ------ Superposition
% 7.64/1.49  
% 7.64/1.49  sup_time_total:                         0.
% 7.64/1.49  sup_time_generating:                    0.
% 7.64/1.49  sup_time_sim_full:                      0.
% 7.64/1.49  sup_time_sim_immed:                     0.
% 7.64/1.49  
% 7.64/1.49  sup_num_of_clauses:                     817
% 7.64/1.49  sup_num_in_active:                      149
% 7.64/1.49  sup_num_in_passive:                     668
% 7.64/1.49  sup_num_of_loops:                       201
% 7.64/1.49  sup_fw_superposition:                   1145
% 7.64/1.49  sup_bw_superposition:                   1104
% 7.64/1.49  sup_immediate_simplified:               1278
% 7.64/1.49  sup_given_eliminated:                   5
% 7.64/1.49  comparisons_done:                       0
% 7.64/1.49  comparisons_avoided:                    0
% 7.64/1.49  
% 7.64/1.49  ------ Simplifications
% 7.64/1.49  
% 7.64/1.49  
% 7.64/1.49  sim_fw_subset_subsumed:                 5
% 7.64/1.49  sim_bw_subset_subsumed:                 4
% 7.64/1.49  sim_fw_subsumed:                        339
% 7.64/1.49  sim_bw_subsumed:                        18
% 7.64/1.49  sim_fw_subsumption_res:                 0
% 7.64/1.49  sim_bw_subsumption_res:                 0
% 7.64/1.49  sim_tautology_del:                      20
% 7.64/1.49  sim_eq_tautology_del:                   315
% 7.64/1.49  sim_eq_res_simp:                        5
% 7.64/1.49  sim_fw_demodulated:                     594
% 7.64/1.49  sim_bw_demodulated:                     135
% 7.64/1.49  sim_light_normalised:                   691
% 7.64/1.49  sim_joinable_taut:                      0
% 7.64/1.49  sim_joinable_simp:                      0
% 7.64/1.49  sim_ac_normalised:                      0
% 7.64/1.49  sim_smt_subsumption:                    0
% 7.64/1.49  
%------------------------------------------------------------------------------
