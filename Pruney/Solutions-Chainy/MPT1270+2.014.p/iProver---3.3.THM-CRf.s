%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:16 EST 2020

% Result     : Theorem 35.34s
% Output     : CNFRefutation 35.34s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 919 expanded)
%              Number of clauses        :  124 ( 351 expanded)
%              Number of leaves         :   17 ( 184 expanded)
%              Depth                    :   25
%              Number of atoms          :  429 (3155 expanded)
%              Number of equality atoms :  171 ( 598 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(sK1,k2_tops_1(X0,sK1))
          | ~ v2_tops_1(sK1,X0) )
        & ( r1_tarski(sK1,k2_tops_1(X0,sK1))
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_137405,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_137398,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_137612,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_137405,c_137398])).

cnf(c_25,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_231,plain,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_23,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_376,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_377,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,X0) = k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_231,c_377])).

cnf(c_492,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_624,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_26,c_492])).

cnf(c_59100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_59096,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_59227,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_59100,c_59096])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_59104,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_59105,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_59505,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_59104,c_59105])).

cnf(c_60740,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(X0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_59227,c_59505])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_59110,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_60735,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_59110,c_59505])).

cnf(c_61104,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k1_tops_1(sK0,sK1)) = k4_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_60740,c_60735])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_59109,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_60736,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_59109,c_59505])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_59106,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_60865,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_60736,c_59106])).

cnf(c_61477,plain,
    ( r1_xboole_0(k4_xboole_0(k1_tops_1(sK0,sK1),X0),k4_xboole_0(X1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_61104,c_60865])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_59108,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_63691,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_61477,c_59108])).

cnf(c_63979,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_63691,c_59106])).

cnf(c_37069,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_37075,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_37071,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_37080,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_37648,plain,
    ( k4_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_37071,c_37080])).

cnf(c_37764,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_37075,c_37648])).

cnf(c_37079,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_38100,plain,
    ( r1_xboole_0(X0,k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37764,c_37079])).

cnf(c_38674,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_37069,c_38100])).

cnf(c_41627,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_38674,c_37080])).

cnf(c_37085,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_38105,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_37079,c_37080])).

cnf(c_42980,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_37085,c_38105])).

cnf(c_37081,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_43238,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_42980,c_37081])).

cnf(c_43338,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_41627,c_43238])).

cnf(c_64654,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_63979,c_43338])).

cnf(c_64659,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_64654,c_59105])).

cnf(c_64660,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_64659,c_63691])).

cnf(c_137226,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_64660])).

cnf(c_137693,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_137612,c_137226])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_137396,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_137406,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_137899,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_137396,c_137406])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_228,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_227])).

cnf(c_276,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_228])).

cnf(c_137404,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_138053,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_137899,c_137404])).

cnf(c_139898,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_137405,c_138053])).

cnf(c_140015,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_137693,c_139898])).

cnf(c_6,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_137412,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_137410,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_137862,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_137412,c_137410])).

cnf(c_137409,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_138454,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_137862,c_137409])).

cnf(c_33207,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_33206,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_14,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_33200,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_33198,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_33982,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_33200,c_33198])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_33208,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_34425,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_33982,c_33208])).

cnf(c_34796,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_33206,c_34425])).

cnf(c_33201,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_35250,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_34796,c_33201])).

cnf(c_35660,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_33207,c_35250])).

cnf(c_139223,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_138454,c_35660])).

cnf(c_139229,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_139223,c_137410])).

cnf(c_140017,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_140015,c_139229])).

cnf(c_24,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_229,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_22,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_391,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_392,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_229,c_392])).

cnf(c_506,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_622,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_26,c_506])).

cnf(c_508,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_26])).

cnf(c_137221,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_508,c_64660])).

cnf(c_137395,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137221])).

cnf(c_161116,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_140017,c_137395])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_444,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_446,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_29,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_161116,c_446,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.34/5.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.34/5.00  
% 35.34/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.34/5.00  
% 35.34/5.00  ------  iProver source info
% 35.34/5.00  
% 35.34/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.34/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.34/5.00  git: non_committed_changes: false
% 35.34/5.00  git: last_make_outside_of_git: false
% 35.34/5.00  
% 35.34/5.00  ------ 
% 35.34/5.00  ------ Parsing...
% 35.34/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  ------ Proving...
% 35.34/5.00  ------ Problem Properties 
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  clauses                                 24
% 35.34/5.00  conjectures                             1
% 35.34/5.00  EPR                                     4
% 35.34/5.00  Horn                                    23
% 35.34/5.00  unary                                   5
% 35.34/5.00  binary                                  17
% 35.34/5.00  lits                                    45
% 35.34/5.00  lits eq                                 9
% 35.34/5.00  fd_pure                                 0
% 35.34/5.00  fd_pseudo                               0
% 35.34/5.00  fd_cond                                 1
% 35.34/5.00  fd_pseudo_cond                          1
% 35.34/5.00  AC symbols                              0
% 35.34/5.00  
% 35.34/5.00  ------ Input Options Time Limit: Unbounded
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 35.34/5.00  Current options:
% 35.34/5.00  ------ 
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.34/5.00  
% 35.34/5.00  ------ Proving...
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  % SZS status Theorem for theBenchmark.p
% 35.34/5.00  
% 35.34/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.34/5.00  
% 35.34/5.00  fof(f18,conjecture,(
% 35.34/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f19,negated_conjecture,(
% 35.34/5.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 35.34/5.00    inference(negated_conjecture,[],[f18])).
% 35.34/5.00  
% 35.34/5.00  fof(f33,plain,(
% 35.34/5.00    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 35.34/5.00    inference(ennf_transformation,[],[f19])).
% 35.34/5.00  
% 35.34/5.00  fof(f39,plain,(
% 35.34/5.00    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 35.34/5.00    inference(nnf_transformation,[],[f33])).
% 35.34/5.00  
% 35.34/5.00  fof(f40,plain,(
% 35.34/5.00    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 35.34/5.00    inference(flattening,[],[f39])).
% 35.34/5.00  
% 35.34/5.00  fof(f42,plain,(
% 35.34/5.00    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~r1_tarski(sK1,k2_tops_1(X0,sK1)) | ~v2_tops_1(sK1,X0)) & (r1_tarski(sK1,k2_tops_1(X0,sK1)) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.34/5.00    introduced(choice_axiom,[])).
% 35.34/5.00  
% 35.34/5.00  fof(f41,plain,(
% 35.34/5.00    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 35.34/5.00    introduced(choice_axiom,[])).
% 35.34/5.00  
% 35.34/5.00  fof(f43,plain,(
% 35.34/5.00    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 35.34/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 35.34/5.00  
% 35.34/5.00  fof(f69,plain,(
% 35.34/5.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 35.34/5.00    inference(cnf_transformation,[],[f43])).
% 35.34/5.00  
% 35.34/5.00  fof(f14,axiom,(
% 35.34/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f29,plain,(
% 35.34/5.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.34/5.00    inference(ennf_transformation,[],[f14])).
% 35.34/5.00  
% 35.34/5.00  fof(f63,plain,(
% 35.34/5.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f29])).
% 35.34/5.00  
% 35.34/5.00  fof(f68,plain,(
% 35.34/5.00    l1_pre_topc(sK0)),
% 35.34/5.00    inference(cnf_transformation,[],[f43])).
% 35.34/5.00  
% 35.34/5.00  fof(f70,plain,(
% 35.34/5.00    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 35.34/5.00    inference(cnf_transformation,[],[f43])).
% 35.34/5.00  
% 35.34/5.00  fof(f17,axiom,(
% 35.34/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f32,plain,(
% 35.34/5.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.34/5.00    inference(ennf_transformation,[],[f17])).
% 35.34/5.00  
% 35.34/5.00  fof(f38,plain,(
% 35.34/5.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.34/5.00    inference(nnf_transformation,[],[f32])).
% 35.34/5.00  
% 35.34/5.00  fof(f66,plain,(
% 35.34/5.00    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f38])).
% 35.34/5.00  
% 35.34/5.00  fof(f15,axiom,(
% 35.34/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f30,plain,(
% 35.34/5.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.34/5.00    inference(ennf_transformation,[],[f15])).
% 35.34/5.00  
% 35.34/5.00  fof(f64,plain,(
% 35.34/5.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f30])).
% 35.34/5.00  
% 35.34/5.00  fof(f7,axiom,(
% 35.34/5.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f24,plain,(
% 35.34/5.00    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 35.34/5.00    inference(ennf_transformation,[],[f7])).
% 35.34/5.00  
% 35.34/5.00  fof(f56,plain,(
% 35.34/5.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f24])).
% 35.34/5.00  
% 35.34/5.00  fof(f6,axiom,(
% 35.34/5.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f36,plain,(
% 35.34/5.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 35.34/5.00    inference(nnf_transformation,[],[f6])).
% 35.34/5.00  
% 35.34/5.00  fof(f54,plain,(
% 35.34/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f36])).
% 35.34/5.00  
% 35.34/5.00  fof(f1,axiom,(
% 35.34/5.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f34,plain,(
% 35.34/5.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.34/5.00    inference(nnf_transformation,[],[f1])).
% 35.34/5.00  
% 35.34/5.00  fof(f35,plain,(
% 35.34/5.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.34/5.00    inference(flattening,[],[f34])).
% 35.34/5.00  
% 35.34/5.00  fof(f44,plain,(
% 35.34/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.34/5.00    inference(cnf_transformation,[],[f35])).
% 35.34/5.00  
% 35.34/5.00  fof(f73,plain,(
% 35.34/5.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.34/5.00    inference(equality_resolution,[],[f44])).
% 35.34/5.00  
% 35.34/5.00  fof(f3,axiom,(
% 35.34/5.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f48,plain,(
% 35.34/5.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f3])).
% 35.34/5.00  
% 35.34/5.00  fof(f55,plain,(
% 35.34/5.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 35.34/5.00    inference(cnf_transformation,[],[f36])).
% 35.34/5.00  
% 35.34/5.00  fof(f4,axiom,(
% 35.34/5.00    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f22,plain,(
% 35.34/5.00    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 35.34/5.00    inference(ennf_transformation,[],[f4])).
% 35.34/5.00  
% 35.34/5.00  fof(f50,plain,(
% 35.34/5.00    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 35.34/5.00    inference(cnf_transformation,[],[f22])).
% 35.34/5.00  
% 35.34/5.00  fof(f16,axiom,(
% 35.34/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f31,plain,(
% 35.34/5.00    ! [X0] : (! [X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.34/5.00    inference(ennf_transformation,[],[f16])).
% 35.34/5.00  
% 35.34/5.00  fof(f65,plain,(
% 35.34/5.00    ( ! [X0,X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f31])).
% 35.34/5.00  
% 35.34/5.00  fof(f12,axiom,(
% 35.34/5.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f26,plain,(
% 35.34/5.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 35.34/5.00    inference(ennf_transformation,[],[f12])).
% 35.34/5.00  
% 35.34/5.00  fof(f27,plain,(
% 35.34/5.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 35.34/5.00    inference(flattening,[],[f26])).
% 35.34/5.00  
% 35.34/5.00  fof(f61,plain,(
% 35.34/5.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f27])).
% 35.34/5.00  
% 35.34/5.00  fof(f10,axiom,(
% 35.34/5.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f37,plain,(
% 35.34/5.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 35.34/5.00    inference(nnf_transformation,[],[f10])).
% 35.34/5.00  
% 35.34/5.00  fof(f59,plain,(
% 35.34/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 35.34/5.00    inference(cnf_transformation,[],[f37])).
% 35.34/5.00  
% 35.34/5.00  fof(f8,axiom,(
% 35.34/5.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f25,plain,(
% 35.34/5.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.34/5.00    inference(ennf_transformation,[],[f8])).
% 35.34/5.00  
% 35.34/5.00  fof(f57,plain,(
% 35.34/5.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.34/5.00    inference(cnf_transformation,[],[f25])).
% 35.34/5.00  
% 35.34/5.00  fof(f60,plain,(
% 35.34/5.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f37])).
% 35.34/5.00  
% 35.34/5.00  fof(f49,plain,(
% 35.34/5.00    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f22])).
% 35.34/5.00  
% 35.34/5.00  fof(f74,plain,(
% 35.34/5.00    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 35.34/5.00    inference(equality_resolution,[],[f49])).
% 35.34/5.00  
% 35.34/5.00  fof(f9,axiom,(
% 35.34/5.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f58,plain,(
% 35.34/5.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 35.34/5.00    inference(cnf_transformation,[],[f9])).
% 35.34/5.00  
% 35.34/5.00  fof(f46,plain,(
% 35.34/5.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f35])).
% 35.34/5.00  
% 35.34/5.00  fof(f71,plain,(
% 35.34/5.00    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 35.34/5.00    inference(cnf_transformation,[],[f43])).
% 35.34/5.00  
% 35.34/5.00  fof(f67,plain,(
% 35.34/5.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f38])).
% 35.34/5.00  
% 35.34/5.00  fof(f13,axiom,(
% 35.34/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 35.34/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.34/5.00  
% 35.34/5.00  fof(f28,plain,(
% 35.34/5.00    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.34/5.00    inference(ennf_transformation,[],[f13])).
% 35.34/5.00  
% 35.34/5.00  fof(f62,plain,(
% 35.34/5.00    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.34/5.00    inference(cnf_transformation,[],[f28])).
% 35.34/5.00  
% 35.34/5.00  cnf(c_26,negated_conjecture,
% 35.34/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.34/5.00      inference(cnf_transformation,[],[f69]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137405,plain,
% 35.34/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_19,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | ~ l1_pre_topc(X1)
% 35.34/5.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 35.34/5.00      inference(cnf_transformation,[],[f63]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_27,negated_conjecture,
% 35.34/5.00      ( l1_pre_topc(sK0) ),
% 35.34/5.00      inference(cnf_transformation,[],[f68]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_430,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 35.34/5.00      | sK0 != X1 ),
% 35.34/5.00      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_431,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.34/5.00      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 35.34/5.00      inference(unflattening,[status(thm)],[c_430]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137398,plain,
% 35.34/5.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 35.34/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137612,plain,
% 35.34/5.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_137405,c_137398]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_25,negated_conjecture,
% 35.34/5.00      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 35.34/5.00      inference(cnf_transformation,[],[f70]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_231,plain,
% 35.34/5.00      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 35.34/5.00      inference(prop_impl,[status(thm)],[c_25]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_23,plain,
% 35.34/5.00      ( ~ v2_tops_1(X0,X1)
% 35.34/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | ~ l1_pre_topc(X1)
% 35.34/5.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 35.34/5.00      inference(cnf_transformation,[],[f66]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_376,plain,
% 35.34/5.00      ( ~ v2_tops_1(X0,X1)
% 35.34/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | k1_tops_1(X1,X0) = k1_xboole_0
% 35.34/5.00      | sK0 != X1 ),
% 35.34/5.00      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_377,plain,
% 35.34/5.00      ( ~ v2_tops_1(X0,sK0)
% 35.34/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.34/5.00      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 35.34/5.00      inference(unflattening,[status(thm)],[c_376]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_491,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.34/5.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 35.34/5.00      | k1_tops_1(sK0,X0) = k1_xboole_0
% 35.34/5.00      | sK0 != sK0
% 35.34/5.00      | sK1 != X0 ),
% 35.34/5.00      inference(resolution_lifted,[status(thm)],[c_231,c_377]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_492,plain,
% 35.34/5.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.34/5.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 35.34/5.00      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 35.34/5.00      inference(unflattening,[status(thm)],[c_491]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_624,plain,
% 35.34/5.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 35.34/5.00      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 35.34/5.00      inference(prop_impl,[status(thm)],[c_26,c_492]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_59100,plain,
% 35.34/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_20,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 35.34/5.00      | ~ l1_pre_topc(X1) ),
% 35.34/5.00      inference(cnf_transformation,[],[f64]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_418,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 35.34/5.00      | sK0 != X1 ),
% 35.34/5.00      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_419,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.34/5.00      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 35.34/5.00      inference(unflattening,[status(thm)],[c_418]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_59096,plain,
% 35.34/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.34/5.00      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_59227,plain,
% 35.34/5.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_59100,c_59096]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_12,plain,
% 35.34/5.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 35.34/5.00      inference(cnf_transformation,[],[f56]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_59104,plain,
% 35.34/5.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 35.34/5.00      | r1_tarski(X0,X2) != iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_11,plain,
% 35.34/5.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 35.34/5.00      inference(cnf_transformation,[],[f54]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_59105,plain,
% 35.34/5.00      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_59505,plain,
% 35.34/5.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
% 35.34/5.00      | r1_tarski(X0,X2) != iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_59104,c_59105]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_60740,plain,
% 35.34/5.00      ( k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(X0,sK1)) = k1_tops_1(sK0,sK1) ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_59227,c_59505]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_2,plain,
% 35.34/5.00      ( r1_tarski(X0,X0) ),
% 35.34/5.00      inference(cnf_transformation,[],[f73]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_59110,plain,
% 35.34/5.00      ( r1_tarski(X0,X0) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_60735,plain,
% 35.34/5.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_59110,c_59505]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_61104,plain,
% 35.34/5.00      ( k4_xboole_0(k4_xboole_0(X0,sK1),k1_tops_1(sK0,sK1)) = k4_xboole_0(X0,sK1) ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_60740,c_60735]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_4,plain,
% 35.34/5.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 35.34/5.00      inference(cnf_transformation,[],[f48]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_59109,plain,
% 35.34/5.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_60736,plain,
% 35.34/5.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_59109,c_59505]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_10,plain,
% 35.34/5.00      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 35.34/5.00      inference(cnf_transformation,[],[f55]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_59106,plain,
% 35.34/5.00      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_60865,plain,
% 35.34/5.00      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_60736,c_59106]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_61477,plain,
% 35.34/5.00      ( r1_xboole_0(k4_xboole_0(k1_tops_1(sK0,sK1),X0),k4_xboole_0(X1,sK1)) = iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_61104,c_60865]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_5,plain,
% 35.34/5.00      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 35.34/5.00      inference(cnf_transformation,[],[f50]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_59108,plain,
% 35.34/5.00      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_63691,plain,
% 35.34/5.00      ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_61477,c_59108]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_63979,plain,
% 35.34/5.00      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 35.34/5.00      | r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_63691,c_59106]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_37069,plain,
% 35.34/5.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 35.34/5.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_37075,plain,
% 35.34/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_21,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
% 35.34/5.00      | ~ l1_pre_topc(X1) ),
% 35.34/5.00      inference(cnf_transformation,[],[f65]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_406,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
% 35.34/5.00      | sK0 != X1 ),
% 35.34/5.00      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_407,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.34/5.00      | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) ),
% 35.34/5.00      inference(unflattening,[status(thm)],[c_406]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_37071,plain,
% 35.34/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.34/5.00      | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_37080,plain,
% 35.34/5.00      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_37648,plain,
% 35.34/5.00      ( k4_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 35.34/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_37071,c_37080]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_37764,plain,
% 35.34/5.00      ( k4_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_37075,c_37648]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_37079,plain,
% 35.34/5.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 35.34/5.00      | r1_tarski(X0,X2) != iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_38100,plain,
% 35.34/5.00      ( r1_xboole_0(X0,k1_tops_1(sK0,sK1)) = iProver_top
% 35.34/5.00      | r1_tarski(X0,k2_tops_1(sK0,sK1)) != iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_37764,c_37079]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_38674,plain,
% 35.34/5.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 35.34/5.00      | r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) = iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_37069,c_38100]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_41627,plain,
% 35.34/5.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 35.34/5.00      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1 ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_38674,c_37080]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_37085,plain,
% 35.34/5.00      ( r1_tarski(X0,X0) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_38105,plain,
% 35.34/5.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
% 35.34/5.00      | r1_tarski(X0,X2) != iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_37079,c_37080]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_42980,plain,
% 35.34/5.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_37085,c_38105]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_37081,plain,
% 35.34/5.00      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_43238,plain,
% 35.34/5.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_42980,c_37081]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_43338,plain,
% 35.34/5.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 35.34/5.00      | r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_41627,c_43238]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_64654,plain,
% 35.34/5.00      ( r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 35.34/5.00      inference(global_propositional_subsumption,
% 35.34/5.00                [status(thm)],
% 35.34/5.00                [c_63979,c_43338]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_64659,plain,
% 35.34/5.00      ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_tops_1(sK0,sK1) ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_64654,c_59105]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_64660,plain,
% 35.34/5.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 35.34/5.00      inference(light_normalisation,[status(thm)],[c_64659,c_63691]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137226,plain,
% 35.34/5.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 35.34/5.00      inference(global_propositional_subsumption,
% 35.34/5.00                [status(thm)],
% 35.34/5.00                [c_624,c_64660]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137693,plain,
% 35.34/5.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 35.34/5.00      inference(light_normalisation,[status(thm)],[c_137612,c_137226]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_17,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | ~ l1_pre_topc(X1) ),
% 35.34/5.00      inference(cnf_transformation,[],[f61]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_454,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | sK0 != X1 ),
% 35.34/5.00      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_455,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.34/5.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.34/5.00      inference(unflattening,[status(thm)],[c_454]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137396,plain,
% 35.34/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.34/5.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_16,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 35.34/5.00      inference(cnf_transformation,[],[f59]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137406,plain,
% 35.34/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.34/5.00      | r1_tarski(X0,X1) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137899,plain,
% 35.34/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.34/5.00      | r1_tarski(k2_pre_topc(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_137396,c_137406]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_13,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.34/5.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 35.34/5.00      inference(cnf_transformation,[],[f57]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_15,plain,
% 35.34/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.34/5.00      inference(cnf_transformation,[],[f60]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_227,plain,
% 35.34/5.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 35.34/5.00      inference(prop_impl,[status(thm)],[c_15]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_228,plain,
% 35.34/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.34/5.00      inference(renaming,[status(thm)],[c_227]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_276,plain,
% 35.34/5.00      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 35.34/5.00      inference(bin_hyper_res,[status(thm)],[c_13,c_228]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137404,plain,
% 35.34/5.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 35.34/5.00      | r1_tarski(X1,X0) != iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_138053,plain,
% 35.34/5.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)
% 35.34/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_137899,c_137404]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_139898,plain,
% 35.34/5.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_137405,c_138053]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_140015,plain,
% 35.34/5.00      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_137693,c_139898]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_6,plain,
% 35.34/5.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 35.34/5.00      inference(cnf_transformation,[],[f74]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137412,plain,
% 35.34/5.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137410,plain,
% 35.34/5.00      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137862,plain,
% 35.34/5.00      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_137412,c_137410]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137409,plain,
% 35.34/5.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 35.34/5.00      | r1_tarski(X0,X2) != iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_138454,plain,
% 35.34/5.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
% 35.34/5.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_137862,c_137409]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_33207,plain,
% 35.34/5.00      ( r1_tarski(X0,X0) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_33206,plain,
% 35.34/5.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_14,plain,
% 35.34/5.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 35.34/5.00      inference(cnf_transformation,[],[f58]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_33200,plain,
% 35.34/5.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_33198,plain,
% 35.34/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.34/5.00      | r1_tarski(X0,X1) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_33982,plain,
% 35.34/5.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_33200,c_33198]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_0,plain,
% 35.34/5.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 35.34/5.00      inference(cnf_transformation,[],[f46]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_33208,plain,
% 35.34/5.00      ( X0 = X1
% 35.34/5.00      | r1_tarski(X0,X1) != iProver_top
% 35.34/5.00      | r1_tarski(X1,X0) != iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_34425,plain,
% 35.34/5.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_33982,c_33208]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_34796,plain,
% 35.34/5.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_33206,c_34425]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_33201,plain,
% 35.34/5.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 35.34/5.00      | r1_tarski(X0,X2) != iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_35250,plain,
% 35.34/5.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
% 35.34/5.00      | r1_tarski(X0,X1) != iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_34796,c_33201]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_35660,plain,
% 35.34/5.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_33207,c_35250]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_139223,plain,
% 35.34/5.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 35.34/5.00      inference(global_propositional_subsumption,
% 35.34/5.00                [status(thm)],
% 35.34/5.00                [c_138454,c_35660]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_139229,plain,
% 35.34/5.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.34/5.00      inference(superposition,[status(thm)],[c_139223,c_137410]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_140017,plain,
% 35.34/5.00      ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
% 35.34/5.00      inference(demodulation,[status(thm)],[c_140015,c_139229]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_24,negated_conjecture,
% 35.34/5.00      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 35.34/5.00      inference(cnf_transformation,[],[f71]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_229,plain,
% 35.34/5.00      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 35.34/5.00      inference(prop_impl,[status(thm)],[c_24]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_22,plain,
% 35.34/5.00      ( v2_tops_1(X0,X1)
% 35.34/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | ~ l1_pre_topc(X1)
% 35.34/5.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 35.34/5.00      inference(cnf_transformation,[],[f67]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_391,plain,
% 35.34/5.00      ( v2_tops_1(X0,X1)
% 35.34/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | k1_tops_1(X1,X0) != k1_xboole_0
% 35.34/5.00      | sK0 != X1 ),
% 35.34/5.00      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_392,plain,
% 35.34/5.00      ( v2_tops_1(X0,sK0)
% 35.34/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.34/5.00      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 35.34/5.00      inference(unflattening,[status(thm)],[c_391]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_505,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.34/5.00      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 35.34/5.00      | k1_tops_1(sK0,X0) != k1_xboole_0
% 35.34/5.00      | sK0 != sK0
% 35.34/5.00      | sK1 != X0 ),
% 35.34/5.00      inference(resolution_lifted,[status(thm)],[c_229,c_392]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_506,plain,
% 35.34/5.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.34/5.00      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 35.34/5.00      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 35.34/5.00      inference(unflattening,[status(thm)],[c_505]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_622,plain,
% 35.34/5.00      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 35.34/5.00      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 35.34/5.00      inference(prop_impl,[status(thm)],[c_26,c_506]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_508,plain,
% 35.34/5.00      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 35.34/5.00      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 35.34/5.00      inference(global_propositional_subsumption,
% 35.34/5.00                [status(thm)],
% 35.34/5.00                [c_506,c_26]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137221,plain,
% 35.34/5.00      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 35.34/5.00      inference(global_propositional_subsumption,
% 35.34/5.00                [status(thm)],
% 35.34/5.00                [c_622,c_508,c_64660]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_137395,plain,
% 35.34/5.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_137221]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_161116,plain,
% 35.34/5.00      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 35.34/5.00      inference(demodulation,[status(thm)],[c_140017,c_137395]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_18,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 35.34/5.00      | ~ l1_pre_topc(X1) ),
% 35.34/5.00      inference(cnf_transformation,[],[f62]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_442,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.34/5.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 35.34/5.00      | sK0 != X1 ),
% 35.34/5.00      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_443,plain,
% 35.34/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.34/5.00      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 35.34/5.00      inference(unflattening,[status(thm)],[c_442]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_444,plain,
% 35.34/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.34/5.00      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_446,plain,
% 35.34/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.34/5.00      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
% 35.34/5.00      inference(instantiation,[status(thm)],[c_444]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(c_29,plain,
% 35.34/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.34/5.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.34/5.00  
% 35.34/5.00  cnf(contradiction,plain,
% 35.34/5.00      ( $false ),
% 35.34/5.00      inference(minisat,[status(thm)],[c_161116,c_446,c_29]) ).
% 35.34/5.00  
% 35.34/5.00  
% 35.34/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.34/5.00  
% 35.34/5.00  ------                               Statistics
% 35.34/5.00  
% 35.34/5.00  ------ Selected
% 35.34/5.00  
% 35.34/5.00  total_time:                             4.254
% 35.34/5.00  
%------------------------------------------------------------------------------
