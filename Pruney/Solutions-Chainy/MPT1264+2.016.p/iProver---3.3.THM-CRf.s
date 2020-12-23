%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:54 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 457 expanded)
%              Number of clauses        :   59 ( 129 expanded)
%              Number of leaves         :   15 ( 133 expanded)
%              Depth                    :   17
%              Number of atoms          :  300 (2132 expanded)
%              Number of equality atoms :   99 ( 460 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( v3_pre_topc(X2,X0)
                   => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
          & v3_pre_topc(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_pre_topc(X0,sK3) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK3,X1))
        & v3_pre_topc(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,sK2))
            & v3_pre_topc(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v1_tops_1(sK2,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,X1))
              & v3_pre_topc(X2,sK1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & v1_tops_1(X1,sK1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2))
    & v3_pre_topc(sK3,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & v1_tops_1(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f32,f31,f30])).

fof(f49,plain,(
    v1_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f52,plain,(
    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,negated_conjecture,
    ( v1_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_9,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_260,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_261,plain,
    ( ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = k2_struct_0(sK1)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_261])).

cnf(c_316,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_318,plain,
    ( k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_15])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_291,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_602,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_194,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_5])).

cnf(c_255,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_194,c_16])).

cnf(c_256,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_636,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_602,c_256])).

cnf(c_759,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_318,c_636])).

cnf(c_604,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_615,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_604,c_256])).

cnf(c_852,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_759,c_615])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_606,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_952,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_struct_0(sK1))) = k9_subset_1(k2_struct_0(sK1),X0,k2_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_852,c_606])).

cnf(c_949,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k9_subset_1(k2_struct_0(sK1),X0,sK2) ),
    inference(superposition,[status(thm)],[c_615,c_606])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,negated_conjecture,
    ( v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2))
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_235,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_235,c_17,c_16,c_13])).

cnf(c_603,plain,
    ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_651,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_603,c_256])).

cnf(c_860,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_615,c_651])).

cnf(c_873,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_860,c_318])).

cnf(c_1219,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_949,c_873])).

cnf(c_1463,plain,
    ( k2_pre_topc(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_struct_0(sK1)))) = k2_pre_topc(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_952,c_1219])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_609,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_605,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_618,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_605,c_256])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_607,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1145,plain,
    ( r2_hidden(X0,k2_struct_0(sK1)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_607])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_610,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1358,plain,
    ( r2_hidden(sK0(X0,k2_struct_0(sK1)),sK3) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_610])).

cnf(c_2076,plain,
    ( r1_tarski(sK3,k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_1358])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_608,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2080,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_struct_0(sK1))) = sK3 ),
    inference(superposition,[status(thm)],[c_2076,c_608])).

cnf(c_2783,plain,
    ( k2_pre_topc(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) = k2_pre_topc(sK1,sK3) ),
    inference(light_normalisation,[status(thm)],[c_1463,c_2080])).

cnf(c_11,negated_conjecture,
    ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_621,plain,
    ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,sK2)) != k2_pre_topc(sK1,sK3) ),
    inference(light_normalisation,[status(thm)],[c_11,c_256])).

cnf(c_1220,plain,
    ( k2_pre_topc(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) != k2_pre_topc(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_949,c_621])).

cnf(c_2785,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2783,c_1220])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.45/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/0.98  
% 2.45/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/0.98  
% 2.45/0.98  ------  iProver source info
% 2.45/0.98  
% 2.45/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.45/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/0.98  git: non_committed_changes: false
% 2.45/0.98  git: last_make_outside_of_git: false
% 2.45/0.98  
% 2.45/0.98  ------ 
% 2.45/0.98  
% 2.45/0.98  ------ Input Options
% 2.45/0.98  
% 2.45/0.98  --out_options                           all
% 2.45/0.98  --tptp_safe_out                         true
% 2.45/0.98  --problem_path                          ""
% 2.45/0.98  --include_path                          ""
% 2.45/0.98  --clausifier                            res/vclausify_rel
% 2.45/0.98  --clausifier_options                    --mode clausify
% 2.45/0.98  --stdin                                 false
% 2.45/0.98  --stats_out                             all
% 2.45/0.98  
% 2.45/0.98  ------ General Options
% 2.45/0.98  
% 2.45/0.98  --fof                                   false
% 2.45/0.98  --time_out_real                         305.
% 2.45/0.98  --time_out_virtual                      -1.
% 2.45/0.98  --symbol_type_check                     false
% 2.45/0.98  --clausify_out                          false
% 2.45/0.98  --sig_cnt_out                           false
% 2.45/0.98  --trig_cnt_out                          false
% 2.45/0.98  --trig_cnt_out_tolerance                1.
% 2.45/0.98  --trig_cnt_out_sk_spl                   false
% 2.45/0.98  --abstr_cl_out                          false
% 2.45/0.98  
% 2.45/0.98  ------ Global Options
% 2.45/0.98  
% 2.45/0.98  --schedule                              default
% 2.45/0.98  --add_important_lit                     false
% 2.45/0.98  --prop_solver_per_cl                    1000
% 2.45/0.98  --min_unsat_core                        false
% 2.45/0.98  --soft_assumptions                      false
% 2.45/0.98  --soft_lemma_size                       3
% 2.45/0.98  --prop_impl_unit_size                   0
% 2.45/0.98  --prop_impl_unit                        []
% 2.45/0.98  --share_sel_clauses                     true
% 2.45/0.98  --reset_solvers                         false
% 2.45/0.98  --bc_imp_inh                            [conj_cone]
% 2.45/0.98  --conj_cone_tolerance                   3.
% 2.45/0.98  --extra_neg_conj                        none
% 2.45/0.98  --large_theory_mode                     true
% 2.45/0.98  --prolific_symb_bound                   200
% 2.45/0.98  --lt_threshold                          2000
% 2.45/0.98  --clause_weak_htbl                      true
% 2.45/0.98  --gc_record_bc_elim                     false
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing Options
% 2.45/0.98  
% 2.45/0.98  --preprocessing_flag                    true
% 2.45/0.98  --time_out_prep_mult                    0.1
% 2.45/0.98  --splitting_mode                        input
% 2.45/0.98  --splitting_grd                         true
% 2.45/0.98  --splitting_cvd                         false
% 2.45/0.98  --splitting_cvd_svl                     false
% 2.45/0.98  --splitting_nvd                         32
% 2.45/0.98  --sub_typing                            true
% 2.45/0.98  --prep_gs_sim                           true
% 2.45/0.98  --prep_unflatten                        true
% 2.45/0.98  --prep_res_sim                          true
% 2.45/0.98  --prep_upred                            true
% 2.45/0.98  --prep_sem_filter                       exhaustive
% 2.45/0.98  --prep_sem_filter_out                   false
% 2.45/0.98  --pred_elim                             true
% 2.45/0.98  --res_sim_input                         true
% 2.45/0.98  --eq_ax_congr_red                       true
% 2.45/0.98  --pure_diseq_elim                       true
% 2.45/0.98  --brand_transform                       false
% 2.45/0.98  --non_eq_to_eq                          false
% 2.45/0.98  --prep_def_merge                        true
% 2.45/0.98  --prep_def_merge_prop_impl              false
% 2.45/0.98  --prep_def_merge_mbd                    true
% 2.45/0.98  --prep_def_merge_tr_red                 false
% 2.45/0.98  --prep_def_merge_tr_cl                  false
% 2.45/0.98  --smt_preprocessing                     true
% 2.45/0.98  --smt_ac_axioms                         fast
% 2.45/0.98  --preprocessed_out                      false
% 2.45/0.98  --preprocessed_stats                    false
% 2.45/0.98  
% 2.45/0.98  ------ Abstraction refinement Options
% 2.45/0.98  
% 2.45/0.98  --abstr_ref                             []
% 2.45/0.98  --abstr_ref_prep                        false
% 2.45/0.98  --abstr_ref_until_sat                   false
% 2.45/0.98  --abstr_ref_sig_restrict                funpre
% 2.45/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/0.98  --abstr_ref_under                       []
% 2.45/0.98  
% 2.45/0.98  ------ SAT Options
% 2.45/0.98  
% 2.45/0.98  --sat_mode                              false
% 2.45/0.98  --sat_fm_restart_options                ""
% 2.45/0.98  --sat_gr_def                            false
% 2.45/0.98  --sat_epr_types                         true
% 2.45/0.98  --sat_non_cyclic_types                  false
% 2.45/0.98  --sat_finite_models                     false
% 2.45/0.98  --sat_fm_lemmas                         false
% 2.45/0.98  --sat_fm_prep                           false
% 2.45/0.98  --sat_fm_uc_incr                        true
% 2.45/0.98  --sat_out_model                         small
% 2.45/0.98  --sat_out_clauses                       false
% 2.45/0.98  
% 2.45/0.98  ------ QBF Options
% 2.45/0.98  
% 2.45/0.98  --qbf_mode                              false
% 2.45/0.98  --qbf_elim_univ                         false
% 2.45/0.98  --qbf_dom_inst                          none
% 2.45/0.98  --qbf_dom_pre_inst                      false
% 2.45/0.98  --qbf_sk_in                             false
% 2.45/0.98  --qbf_pred_elim                         true
% 2.45/0.98  --qbf_split                             512
% 2.45/0.98  
% 2.45/0.98  ------ BMC1 Options
% 2.45/0.98  
% 2.45/0.98  --bmc1_incremental                      false
% 2.45/0.98  --bmc1_axioms                           reachable_all
% 2.45/0.98  --bmc1_min_bound                        0
% 2.45/0.98  --bmc1_max_bound                        -1
% 2.45/0.98  --bmc1_max_bound_default                -1
% 2.45/0.98  --bmc1_symbol_reachability              true
% 2.45/0.98  --bmc1_property_lemmas                  false
% 2.45/0.98  --bmc1_k_induction                      false
% 2.45/0.98  --bmc1_non_equiv_states                 false
% 2.45/0.98  --bmc1_deadlock                         false
% 2.45/0.98  --bmc1_ucm                              false
% 2.45/0.98  --bmc1_add_unsat_core                   none
% 2.45/0.98  --bmc1_unsat_core_children              false
% 2.45/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/0.98  --bmc1_out_stat                         full
% 2.45/0.98  --bmc1_ground_init                      false
% 2.45/0.98  --bmc1_pre_inst_next_state              false
% 2.45/0.98  --bmc1_pre_inst_state                   false
% 2.45/0.98  --bmc1_pre_inst_reach_state             false
% 2.45/0.98  --bmc1_out_unsat_core                   false
% 2.45/0.98  --bmc1_aig_witness_out                  false
% 2.45/0.98  --bmc1_verbose                          false
% 2.45/0.98  --bmc1_dump_clauses_tptp                false
% 2.45/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.45/0.98  --bmc1_dump_file                        -
% 2.45/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.45/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.45/0.98  --bmc1_ucm_extend_mode                  1
% 2.45/0.98  --bmc1_ucm_init_mode                    2
% 2.45/0.98  --bmc1_ucm_cone_mode                    none
% 2.45/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.45/0.98  --bmc1_ucm_relax_model                  4
% 2.45/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.45/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/0.98  --bmc1_ucm_layered_model                none
% 2.45/0.98  --bmc1_ucm_max_lemma_size               10
% 2.45/0.98  
% 2.45/0.98  ------ AIG Options
% 2.45/0.98  
% 2.45/0.98  --aig_mode                              false
% 2.45/0.98  
% 2.45/0.98  ------ Instantiation Options
% 2.45/0.98  
% 2.45/0.98  --instantiation_flag                    true
% 2.45/0.98  --inst_sos_flag                         false
% 2.45/0.98  --inst_sos_phase                        true
% 2.45/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/0.98  --inst_lit_sel_side                     num_symb
% 2.45/0.98  --inst_solver_per_active                1400
% 2.45/0.98  --inst_solver_calls_frac                1.
% 2.45/0.98  --inst_passive_queue_type               priority_queues
% 2.45/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/0.98  --inst_passive_queues_freq              [25;2]
% 2.45/0.98  --inst_dismatching                      true
% 2.45/0.98  --inst_eager_unprocessed_to_passive     true
% 2.45/0.98  --inst_prop_sim_given                   true
% 2.45/0.98  --inst_prop_sim_new                     false
% 2.45/0.98  --inst_subs_new                         false
% 2.45/0.98  --inst_eq_res_simp                      false
% 2.45/0.98  --inst_subs_given                       false
% 2.45/0.98  --inst_orphan_elimination               true
% 2.45/0.98  --inst_learning_loop_flag               true
% 2.45/0.98  --inst_learning_start                   3000
% 2.45/0.98  --inst_learning_factor                  2
% 2.45/0.98  --inst_start_prop_sim_after_learn       3
% 2.45/0.98  --inst_sel_renew                        solver
% 2.45/0.98  --inst_lit_activity_flag                true
% 2.45/0.98  --inst_restr_to_given                   false
% 2.45/0.98  --inst_activity_threshold               500
% 2.45/0.98  --inst_out_proof                        true
% 2.45/0.98  
% 2.45/0.98  ------ Resolution Options
% 2.45/0.98  
% 2.45/0.98  --resolution_flag                       true
% 2.45/0.98  --res_lit_sel                           adaptive
% 2.45/0.98  --res_lit_sel_side                      none
% 2.45/0.98  --res_ordering                          kbo
% 2.45/0.98  --res_to_prop_solver                    active
% 2.45/0.98  --res_prop_simpl_new                    false
% 2.45/0.98  --res_prop_simpl_given                  true
% 2.45/0.98  --res_passive_queue_type                priority_queues
% 2.45/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/0.98  --res_passive_queues_freq               [15;5]
% 2.45/0.98  --res_forward_subs                      full
% 2.45/0.98  --res_backward_subs                     full
% 2.45/0.98  --res_forward_subs_resolution           true
% 2.45/0.98  --res_backward_subs_resolution          true
% 2.45/0.98  --res_orphan_elimination                true
% 2.45/0.98  --res_time_limit                        2.
% 2.45/0.98  --res_out_proof                         true
% 2.45/0.98  
% 2.45/0.98  ------ Superposition Options
% 2.45/0.98  
% 2.45/0.98  --superposition_flag                    true
% 2.45/0.98  --sup_passive_queue_type                priority_queues
% 2.45/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.45/0.98  --demod_completeness_check              fast
% 2.45/0.98  --demod_use_ground                      true
% 2.45/0.98  --sup_to_prop_solver                    passive
% 2.45/0.98  --sup_prop_simpl_new                    true
% 2.45/0.98  --sup_prop_simpl_given                  true
% 2.45/0.98  --sup_fun_splitting                     false
% 2.45/0.98  --sup_smt_interval                      50000
% 2.45/0.98  
% 2.45/0.98  ------ Superposition Simplification Setup
% 2.45/0.98  
% 2.45/0.98  --sup_indices_passive                   []
% 2.45/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_full_bw                           [BwDemod]
% 2.45/0.98  --sup_immed_triv                        [TrivRules]
% 2.45/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_immed_bw_main                     []
% 2.45/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.98  
% 2.45/0.98  ------ Combination Options
% 2.45/0.98  
% 2.45/0.98  --comb_res_mult                         3
% 2.45/0.98  --comb_sup_mult                         2
% 2.45/0.98  --comb_inst_mult                        10
% 2.45/0.98  
% 2.45/0.98  ------ Debug Options
% 2.45/0.98  
% 2.45/0.98  --dbg_backtrace                         false
% 2.45/0.98  --dbg_dump_prop_clauses                 false
% 2.45/0.98  --dbg_dump_prop_clauses_file            -
% 2.45/0.98  --dbg_out_stat                          false
% 2.45/0.98  ------ Parsing...
% 2.45/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/0.98  ------ Proving...
% 2.45/0.98  ------ Problem Properties 
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  clauses                                 12
% 2.45/0.98  conjectures                             3
% 2.45/0.98  EPR                                     0
% 2.45/0.98  Horn                                    11
% 2.45/0.98  unary                                   5
% 2.45/0.98  binary                                  6
% 2.45/0.98  lits                                    20
% 2.45/0.98  lits eq                                 6
% 2.45/0.98  fd_pure                                 0
% 2.45/0.98  fd_pseudo                               0
% 2.45/0.98  fd_cond                                 0
% 2.45/0.98  fd_pseudo_cond                          0
% 2.45/0.98  AC symbols                              0
% 2.45/0.98  
% 2.45/0.98  ------ Schedule dynamic 5 is on 
% 2.45/0.98  
% 2.45/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  ------ 
% 2.45/0.98  Current options:
% 2.45/0.98  ------ 
% 2.45/0.98  
% 2.45/0.98  ------ Input Options
% 2.45/0.98  
% 2.45/0.98  --out_options                           all
% 2.45/0.98  --tptp_safe_out                         true
% 2.45/0.98  --problem_path                          ""
% 2.45/0.98  --include_path                          ""
% 2.45/0.98  --clausifier                            res/vclausify_rel
% 2.45/0.98  --clausifier_options                    --mode clausify
% 2.45/0.98  --stdin                                 false
% 2.45/0.98  --stats_out                             all
% 2.45/0.98  
% 2.45/0.98  ------ General Options
% 2.45/0.98  
% 2.45/0.98  --fof                                   false
% 2.45/0.98  --time_out_real                         305.
% 2.45/0.98  --time_out_virtual                      -1.
% 2.45/0.98  --symbol_type_check                     false
% 2.45/0.98  --clausify_out                          false
% 2.45/0.98  --sig_cnt_out                           false
% 2.45/0.98  --trig_cnt_out                          false
% 2.45/0.98  --trig_cnt_out_tolerance                1.
% 2.45/0.98  --trig_cnt_out_sk_spl                   false
% 2.45/0.98  --abstr_cl_out                          false
% 2.45/0.98  
% 2.45/0.98  ------ Global Options
% 2.45/0.98  
% 2.45/0.98  --schedule                              default
% 2.45/0.98  --add_important_lit                     false
% 2.45/0.98  --prop_solver_per_cl                    1000
% 2.45/0.98  --min_unsat_core                        false
% 2.45/0.98  --soft_assumptions                      false
% 2.45/0.98  --soft_lemma_size                       3
% 2.45/0.98  --prop_impl_unit_size                   0
% 2.45/0.98  --prop_impl_unit                        []
% 2.45/0.98  --share_sel_clauses                     true
% 2.45/0.98  --reset_solvers                         false
% 2.45/0.98  --bc_imp_inh                            [conj_cone]
% 2.45/0.98  --conj_cone_tolerance                   3.
% 2.45/0.98  --extra_neg_conj                        none
% 2.45/0.98  --large_theory_mode                     true
% 2.45/0.98  --prolific_symb_bound                   200
% 2.45/0.98  --lt_threshold                          2000
% 2.45/0.98  --clause_weak_htbl                      true
% 2.45/0.98  --gc_record_bc_elim                     false
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing Options
% 2.45/0.98  
% 2.45/0.98  --preprocessing_flag                    true
% 2.45/0.98  --time_out_prep_mult                    0.1
% 2.45/0.98  --splitting_mode                        input
% 2.45/0.98  --splitting_grd                         true
% 2.45/0.98  --splitting_cvd                         false
% 2.45/0.98  --splitting_cvd_svl                     false
% 2.45/0.98  --splitting_nvd                         32
% 2.45/0.98  --sub_typing                            true
% 2.45/0.98  --prep_gs_sim                           true
% 2.45/0.98  --prep_unflatten                        true
% 2.45/0.98  --prep_res_sim                          true
% 2.45/0.98  --prep_upred                            true
% 2.45/0.98  --prep_sem_filter                       exhaustive
% 2.45/0.98  --prep_sem_filter_out                   false
% 2.45/0.98  --pred_elim                             true
% 2.45/0.98  --res_sim_input                         true
% 2.45/0.98  --eq_ax_congr_red                       true
% 2.45/0.98  --pure_diseq_elim                       true
% 2.45/0.98  --brand_transform                       false
% 2.45/0.98  --non_eq_to_eq                          false
% 2.45/0.98  --prep_def_merge                        true
% 2.45/0.98  --prep_def_merge_prop_impl              false
% 2.45/0.98  --prep_def_merge_mbd                    true
% 2.45/0.98  --prep_def_merge_tr_red                 false
% 2.45/0.98  --prep_def_merge_tr_cl                  false
% 2.45/0.98  --smt_preprocessing                     true
% 2.45/0.98  --smt_ac_axioms                         fast
% 2.45/0.98  --preprocessed_out                      false
% 2.45/0.98  --preprocessed_stats                    false
% 2.45/0.98  
% 2.45/0.98  ------ Abstraction refinement Options
% 2.45/0.98  
% 2.45/0.98  --abstr_ref                             []
% 2.45/0.98  --abstr_ref_prep                        false
% 2.45/0.98  --abstr_ref_until_sat                   false
% 2.45/0.98  --abstr_ref_sig_restrict                funpre
% 2.45/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/0.98  --abstr_ref_under                       []
% 2.45/0.98  
% 2.45/0.98  ------ SAT Options
% 2.45/0.98  
% 2.45/0.98  --sat_mode                              false
% 2.45/0.98  --sat_fm_restart_options                ""
% 2.45/0.98  --sat_gr_def                            false
% 2.45/0.98  --sat_epr_types                         true
% 2.45/0.98  --sat_non_cyclic_types                  false
% 2.45/0.98  --sat_finite_models                     false
% 2.45/0.98  --sat_fm_lemmas                         false
% 2.45/0.98  --sat_fm_prep                           false
% 2.45/0.98  --sat_fm_uc_incr                        true
% 2.45/0.98  --sat_out_model                         small
% 2.45/0.98  --sat_out_clauses                       false
% 2.45/0.98  
% 2.45/0.98  ------ QBF Options
% 2.45/0.98  
% 2.45/0.98  --qbf_mode                              false
% 2.45/0.98  --qbf_elim_univ                         false
% 2.45/0.98  --qbf_dom_inst                          none
% 2.45/0.98  --qbf_dom_pre_inst                      false
% 2.45/0.98  --qbf_sk_in                             false
% 2.45/0.98  --qbf_pred_elim                         true
% 2.45/0.98  --qbf_split                             512
% 2.45/0.98  
% 2.45/0.98  ------ BMC1 Options
% 2.45/0.98  
% 2.45/0.98  --bmc1_incremental                      false
% 2.45/0.98  --bmc1_axioms                           reachable_all
% 2.45/0.98  --bmc1_min_bound                        0
% 2.45/0.98  --bmc1_max_bound                        -1
% 2.45/0.98  --bmc1_max_bound_default                -1
% 2.45/0.98  --bmc1_symbol_reachability              true
% 2.45/0.98  --bmc1_property_lemmas                  false
% 2.45/0.98  --bmc1_k_induction                      false
% 2.45/0.98  --bmc1_non_equiv_states                 false
% 2.45/0.98  --bmc1_deadlock                         false
% 2.45/0.98  --bmc1_ucm                              false
% 2.45/0.98  --bmc1_add_unsat_core                   none
% 2.45/0.98  --bmc1_unsat_core_children              false
% 2.45/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/0.98  --bmc1_out_stat                         full
% 2.45/0.98  --bmc1_ground_init                      false
% 2.45/0.98  --bmc1_pre_inst_next_state              false
% 2.45/0.98  --bmc1_pre_inst_state                   false
% 2.45/0.98  --bmc1_pre_inst_reach_state             false
% 2.45/0.98  --bmc1_out_unsat_core                   false
% 2.45/0.98  --bmc1_aig_witness_out                  false
% 2.45/0.98  --bmc1_verbose                          false
% 2.45/0.98  --bmc1_dump_clauses_tptp                false
% 2.45/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.45/0.98  --bmc1_dump_file                        -
% 2.45/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.45/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.45/0.98  --bmc1_ucm_extend_mode                  1
% 2.45/0.98  --bmc1_ucm_init_mode                    2
% 2.45/0.98  --bmc1_ucm_cone_mode                    none
% 2.45/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.45/0.98  --bmc1_ucm_relax_model                  4
% 2.45/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.45/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/0.98  --bmc1_ucm_layered_model                none
% 2.45/0.98  --bmc1_ucm_max_lemma_size               10
% 2.45/0.98  
% 2.45/0.98  ------ AIG Options
% 2.45/0.98  
% 2.45/0.98  --aig_mode                              false
% 2.45/0.98  
% 2.45/0.98  ------ Instantiation Options
% 2.45/0.98  
% 2.45/0.98  --instantiation_flag                    true
% 2.45/0.98  --inst_sos_flag                         false
% 2.45/0.98  --inst_sos_phase                        true
% 2.45/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/0.98  --inst_lit_sel_side                     none
% 2.45/0.98  --inst_solver_per_active                1400
% 2.45/0.98  --inst_solver_calls_frac                1.
% 2.45/0.98  --inst_passive_queue_type               priority_queues
% 2.45/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/0.98  --inst_passive_queues_freq              [25;2]
% 2.45/0.98  --inst_dismatching                      true
% 2.45/0.98  --inst_eager_unprocessed_to_passive     true
% 2.45/0.98  --inst_prop_sim_given                   true
% 2.45/0.98  --inst_prop_sim_new                     false
% 2.45/0.98  --inst_subs_new                         false
% 2.45/0.98  --inst_eq_res_simp                      false
% 2.45/0.98  --inst_subs_given                       false
% 2.45/0.98  --inst_orphan_elimination               true
% 2.45/0.98  --inst_learning_loop_flag               true
% 2.45/0.98  --inst_learning_start                   3000
% 2.45/0.98  --inst_learning_factor                  2
% 2.45/0.98  --inst_start_prop_sim_after_learn       3
% 2.45/0.98  --inst_sel_renew                        solver
% 2.45/0.98  --inst_lit_activity_flag                true
% 2.45/0.98  --inst_restr_to_given                   false
% 2.45/0.98  --inst_activity_threshold               500
% 2.45/0.98  --inst_out_proof                        true
% 2.45/0.98  
% 2.45/0.98  ------ Resolution Options
% 2.45/0.98  
% 2.45/0.98  --resolution_flag                       false
% 2.45/0.98  --res_lit_sel                           adaptive
% 2.45/0.98  --res_lit_sel_side                      none
% 2.45/0.98  --res_ordering                          kbo
% 2.45/0.98  --res_to_prop_solver                    active
% 2.45/0.98  --res_prop_simpl_new                    false
% 2.45/0.98  --res_prop_simpl_given                  true
% 2.45/0.98  --res_passive_queue_type                priority_queues
% 2.45/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/0.98  --res_passive_queues_freq               [15;5]
% 2.45/0.98  --res_forward_subs                      full
% 2.45/0.98  --res_backward_subs                     full
% 2.45/0.98  --res_forward_subs_resolution           true
% 2.45/0.98  --res_backward_subs_resolution          true
% 2.45/0.98  --res_orphan_elimination                true
% 2.45/0.98  --res_time_limit                        2.
% 2.45/0.98  --res_out_proof                         true
% 2.45/0.98  
% 2.45/0.98  ------ Superposition Options
% 2.45/0.98  
% 2.45/0.98  --superposition_flag                    true
% 2.45/0.98  --sup_passive_queue_type                priority_queues
% 2.45/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.45/0.98  --demod_completeness_check              fast
% 2.45/0.98  --demod_use_ground                      true
% 2.45/0.98  --sup_to_prop_solver                    passive
% 2.45/0.98  --sup_prop_simpl_new                    true
% 2.45/0.98  --sup_prop_simpl_given                  true
% 2.45/0.98  --sup_fun_splitting                     false
% 2.45/0.98  --sup_smt_interval                      50000
% 2.45/0.98  
% 2.45/0.98  ------ Superposition Simplification Setup
% 2.45/0.98  
% 2.45/0.98  --sup_indices_passive                   []
% 2.45/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_full_bw                           [BwDemod]
% 2.45/0.98  --sup_immed_triv                        [TrivRules]
% 2.45/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_immed_bw_main                     []
% 2.45/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.98  
% 2.45/0.98  ------ Combination Options
% 2.45/0.98  
% 2.45/0.98  --comb_res_mult                         3
% 2.45/0.98  --comb_sup_mult                         2
% 2.45/0.98  --comb_inst_mult                        10
% 2.45/0.98  
% 2.45/0.98  ------ Debug Options
% 2.45/0.98  
% 2.45/0.98  --dbg_backtrace                         false
% 2.45/0.98  --dbg_dump_prop_clauses                 false
% 2.45/0.98  --dbg_dump_prop_clauses_file            -
% 2.45/0.98  --dbg_out_stat                          false
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  ------ Proving...
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  % SZS status Theorem for theBenchmark.p
% 2.45/0.98  
% 2.45/0.98   Resolution empty clause
% 2.45/0.98  
% 2.45/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/0.98  
% 2.45/0.98  fof(f11,conjecture,(
% 2.45/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f12,negated_conjecture,(
% 2.45/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 2.45/0.98    inference(negated_conjecture,[],[f11])).
% 2.45/0.98  
% 2.45/0.98  fof(f25,plain,(
% 2.45/0.98    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f12])).
% 2.45/0.98  
% 2.45/0.98  fof(f26,plain,(
% 2.45/0.98    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.45/0.98    inference(flattening,[],[f25])).
% 2.45/0.98  
% 2.45/0.98  fof(f32,plain,(
% 2.45/0.98    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k2_pre_topc(X0,sK3) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK3,X1)) & v3_pre_topc(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.45/0.98    introduced(choice_axiom,[])).
% 2.45/0.98  
% 2.45/0.98  fof(f31,plain,(
% 2.45/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,sK2)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(sK2,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.45/0.98    introduced(choice_axiom,[])).
% 2.45/0.98  
% 2.45/0.98  fof(f30,plain,(
% 2.45/0.98    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,X1)) & v3_pre_topc(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & v1_tops_1(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.45/0.98    introduced(choice_axiom,[])).
% 2.45/0.98  
% 2.45/0.98  fof(f33,plain,(
% 2.45/0.98    ((k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) & v3_pre_topc(sK3,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & v1_tops_1(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f32,f31,f30])).
% 2.45/0.98  
% 2.45/0.98  fof(f49,plain,(
% 2.45/0.98    v1_tops_1(sK2,sK1)),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f9,axiom,(
% 2.45/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f22,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(ennf_transformation,[],[f9])).
% 2.45/0.98  
% 2.45/0.98  fof(f29,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(nnf_transformation,[],[f22])).
% 2.45/0.98  
% 2.45/0.98  fof(f43,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f29])).
% 2.45/0.98  
% 2.45/0.98  fof(f47,plain,(
% 2.45/0.98    l1_pre_topc(sK1)),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f48,plain,(
% 2.45/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f7,axiom,(
% 2.45/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f19,plain,(
% 2.45/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f7])).
% 2.45/0.98  
% 2.45/0.98  fof(f20,plain,(
% 2.45/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(flattening,[],[f19])).
% 2.45/0.98  
% 2.45/0.98  fof(f41,plain,(
% 2.45/0.98    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f20])).
% 2.45/0.98  
% 2.45/0.98  fof(f8,axiom,(
% 2.45/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f21,plain,(
% 2.45/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(ennf_transformation,[],[f8])).
% 2.45/0.98  
% 2.45/0.98  fof(f42,plain,(
% 2.45/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f21])).
% 2.45/0.98  
% 2.45/0.98  fof(f6,axiom,(
% 2.45/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f18,plain,(
% 2.45/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.45/0.98    inference(ennf_transformation,[],[f6])).
% 2.45/0.98  
% 2.45/0.98  fof(f40,plain,(
% 2.45/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f18])).
% 2.45/0.98  
% 2.45/0.98  fof(f5,axiom,(
% 2.45/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f17,plain,(
% 2.45/0.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f5])).
% 2.45/0.98  
% 2.45/0.98  fof(f39,plain,(
% 2.45/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.45/0.98    inference(cnf_transformation,[],[f17])).
% 2.45/0.98  
% 2.45/0.98  fof(f3,axiom,(
% 2.45/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f37,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.45/0.98    inference(cnf_transformation,[],[f3])).
% 2.45/0.98  
% 2.45/0.98  fof(f54,plain,(
% 2.45/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.45/0.98    inference(definition_unfolding,[],[f39,f37])).
% 2.45/0.98  
% 2.45/0.98  fof(f10,axiom,(
% 2.45/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))))))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f23,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f10])).
% 2.45/0.98  
% 2.45/0.98  fof(f24,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.45/0.98    inference(flattening,[],[f23])).
% 2.45/0.98  
% 2.45/0.98  fof(f45,plain,(
% 2.45/0.98    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f24])).
% 2.45/0.98  
% 2.45/0.98  fof(f51,plain,(
% 2.45/0.98    v3_pre_topc(sK3,sK1)),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f46,plain,(
% 2.45/0.98    v2_pre_topc(sK1)),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f50,plain,(
% 2.45/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f1,axiom,(
% 2.45/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f13,plain,(
% 2.45/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 2.45/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 2.45/0.98  
% 2.45/0.98  fof(f14,plain,(
% 2.45/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f13])).
% 2.45/0.98  
% 2.45/0.98  fof(f27,plain,(
% 2.45/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.45/0.98    introduced(choice_axiom,[])).
% 2.45/0.98  
% 2.45/0.98  fof(f28,plain,(
% 2.45/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).
% 2.45/0.98  
% 2.45/0.98  fof(f34,plain,(
% 2.45/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f28])).
% 2.45/0.98  
% 2.45/0.98  fof(f4,axiom,(
% 2.45/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f16,plain,(
% 2.45/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f4])).
% 2.45/0.98  
% 2.45/0.98  fof(f38,plain,(
% 2.45/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.45/0.98    inference(cnf_transformation,[],[f16])).
% 2.45/0.98  
% 2.45/0.98  fof(f35,plain,(
% 2.45/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f28])).
% 2.45/0.98  
% 2.45/0.98  fof(f2,axiom,(
% 2.45/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f15,plain,(
% 2.45/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.45/0.98    inference(ennf_transformation,[],[f2])).
% 2.45/0.98  
% 2.45/0.98  fof(f36,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f15])).
% 2.45/0.98  
% 2.45/0.98  fof(f53,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.45/0.98    inference(definition_unfolding,[],[f36,f37])).
% 2.45/0.98  
% 2.45/0.98  fof(f52,plain,(
% 2.45/0.98    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2))),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  cnf(c_14,negated_conjecture,
% 2.45/0.98      ( v1_tops_1(sK2,sK1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_9,plain,
% 2.45/0.98      ( ~ v1_tops_1(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | ~ l1_pre_topc(X1)
% 2.45/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_16,negated_conjecture,
% 2.45/0.98      ( l1_pre_topc(sK1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_260,plain,
% 2.45/0.98      ( ~ v1_tops_1(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 2.45/0.98      | sK1 != X1 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_261,plain,
% 2.45/0.98      ( ~ v1_tops_1(X0,sK1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | k2_pre_topc(sK1,X0) = k2_struct_0(sK1) ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_260]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_315,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | k2_pre_topc(sK1,X0) = k2_struct_0(sK1)
% 2.45/0.98      | sK2 != X0
% 2.45/0.98      | sK1 != sK1 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_261]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_316,plain,
% 2.45/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_315]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_15,negated_conjecture,
% 2.45/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.45/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_318,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) ),
% 2.45/0.98      inference(global_propositional_subsumption,[status(thm)],[c_316,c_15]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_6,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | ~ l1_pre_topc(X1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_290,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | sK1 != X1 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_291,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_290]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_602,plain,
% 2.45/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.45/0.98      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_7,plain,
% 2.45/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.45/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_5,plain,
% 2.45/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.45/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_194,plain,
% 2.45/0.98      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.45/0.98      inference(resolution,[status(thm)],[c_7,c_5]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_255,plain,
% 2.45/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_194,c_16]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_256,plain,
% 2.45/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_255]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_636,plain,
% 2.45/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.45/0.98      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_602,c_256]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_759,plain,
% 2.45/0.98      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 2.45/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_318,c_636]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_604,plain,
% 2.45/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_615,plain,
% 2.45/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_604,c_256]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_852,plain,
% 2.45/0.98      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 2.45/0.98      inference(global_propositional_subsumption,[status(thm)],[c_759,c_615]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_4,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.45/0.98      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 2.45/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_606,plain,
% 2.45/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 2.45/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_952,plain,
% 2.45/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_struct_0(sK1))) = k9_subset_1(k2_struct_0(sK1),X0,k2_struct_0(sK1)) ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_852,c_606]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_949,plain,
% 2.45/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k9_subset_1(k2_struct_0(sK1),X0,sK2) ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_615,c_606]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_10,plain,
% 2.45/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | ~ v2_pre_topc(X1)
% 2.45/0.98      | ~ l1_pre_topc(X1)
% 2.45/0.98      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) ),
% 2.45/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_12,negated_conjecture,
% 2.45/0.98      ( v3_pre_topc(sK3,sK1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_234,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | ~ v2_pre_topc(X1)
% 2.45/0.98      | ~ l1_pre_topc(X1)
% 2.45/0.98      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2))
% 2.45/0.98      | sK3 != X0
% 2.45/0.98      | sK1 != X1 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_235,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | ~ v2_pre_topc(sK1)
% 2.45/0.98      | ~ l1_pre_topc(sK1)
% 2.45/0.98      | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0)) ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_234]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_17,negated_conjecture,
% 2.45/0.98      ( v2_pre_topc(sK1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_13,negated_conjecture,
% 2.45/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.45/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_239,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0)) ),
% 2.45/0.98      inference(global_propositional_subsumption,
% 2.45/0.98                [status(thm)],
% 2.45/0.98                [c_235,c_17,c_16,c_13]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_603,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,X0))
% 2.45/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_651,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,X0))
% 2.45/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_603,c_256]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_860,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_pre_topc(sK1,sK2))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,sK2)) ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_615,c_651]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_873,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,sK2)) ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_860,c_318]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1219,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_struct_0(sK1))) = k2_pre_topc(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) ),
% 2.45/0.98      inference(demodulation,[status(thm)],[c_949,c_873]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1463,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,k2_struct_0(sK1)))) = k2_pre_topc(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_952,c_1219]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1,plain,
% 2.45/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_609,plain,
% 2.45/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.45/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_605,plain,
% 2.45/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_618,plain,
% 2.45/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_605,c_256]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.45/0.98      | ~ r2_hidden(X2,X0)
% 2.45/0.98      | r2_hidden(X2,X1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_607,plain,
% 2.45/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.45/0.98      | r2_hidden(X2,X0) != iProver_top
% 2.45/0.98      | r2_hidden(X2,X1) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1145,plain,
% 2.45/0.98      ( r2_hidden(X0,k2_struct_0(sK1)) = iProver_top
% 2.45/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_618,c_607]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_0,plain,
% 2.45/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_610,plain,
% 2.45/0.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.45/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1358,plain,
% 2.45/0.98      ( r2_hidden(sK0(X0,k2_struct_0(sK1)),sK3) != iProver_top
% 2.45/0.98      | r1_tarski(X0,k2_struct_0(sK1)) = iProver_top ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_1145,c_610]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_2076,plain,
% 2.45/0.98      ( r1_tarski(sK3,k2_struct_0(sK1)) = iProver_top ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_609,c_1358]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_2,plain,
% 2.45/0.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 2.45/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_608,plain,
% 2.45/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 2.45/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_2080,plain,
% 2.45/0.98      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_struct_0(sK1))) = sK3 ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_2076,c_608]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_2783,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) = k2_pre_topc(sK1,sK3) ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_1463,c_2080]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_11,negated_conjecture,
% 2.45/0.98      ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
% 2.45/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_621,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,sK2)) != k2_pre_topc(sK1,sK3) ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_11,c_256]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1220,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) != k2_pre_topc(sK1,sK3) ),
% 2.45/0.98      inference(demodulation,[status(thm)],[c_949,c_621]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_2785,plain,
% 2.45/0.98      ( $false ),
% 2.45/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_2783,c_1220]) ).
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/0.98  
% 2.45/0.98  ------                               Statistics
% 2.45/0.98  
% 2.45/0.98  ------ General
% 2.45/0.98  
% 2.45/0.98  abstr_ref_over_cycles:                  0
% 2.45/0.98  abstr_ref_under_cycles:                 0
% 2.45/0.98  gc_basic_clause_elim:                   0
% 2.45/0.98  forced_gc_time:                         0
% 2.45/0.98  parsing_time:                           0.01
% 2.45/0.98  unif_index_cands_time:                  0.
% 2.45/0.98  unif_index_add_time:                    0.
% 2.45/0.98  orderings_time:                         0.
% 2.45/0.98  out_proof_time:                         0.009
% 2.45/0.98  total_time:                             0.132
% 2.45/0.98  num_of_symbols:                         49
% 2.45/0.98  num_of_terms:                           2907
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing
% 2.45/0.98  
% 2.45/0.98  num_of_splits:                          0
% 2.45/0.98  num_of_split_atoms:                     0
% 2.45/0.98  num_of_reused_defs:                     0
% 2.45/0.98  num_eq_ax_congr_red:                    20
% 2.45/0.98  num_of_sem_filtered_clauses:            1
% 2.45/0.98  num_of_subtypes:                        0
% 2.45/0.98  monotx_restored_types:                  0
% 2.45/0.98  sat_num_of_epr_types:                   0
% 2.45/0.98  sat_num_of_non_cyclic_types:            0
% 2.45/0.98  sat_guarded_non_collapsed_types:        0
% 2.45/0.98  num_pure_diseq_elim:                    0
% 2.45/0.98  simp_replaced_by:                       0
% 2.45/0.98  res_preprocessed:                       75
% 2.45/0.98  prep_upred:                             0
% 2.45/0.98  prep_unflattend:                        7
% 2.45/0.98  smt_new_axioms:                         0
% 2.45/0.98  pred_elim_cands:                        3
% 2.45/0.98  pred_elim:                              5
% 2.45/0.98  pred_elim_cl:                           6
% 2.45/0.98  pred_elim_cycles:                       8
% 2.45/0.98  merged_defs:                            0
% 2.45/0.98  merged_defs_ncl:                        0
% 2.45/0.98  bin_hyper_res:                          0
% 2.45/0.98  prep_cycles:                            4
% 2.45/0.98  pred_elim_time:                         0.002
% 2.45/0.98  splitting_time:                         0.
% 2.45/0.98  sem_filter_time:                        0.
% 2.45/0.98  monotx_time:                            0.
% 2.45/0.98  subtype_inf_time:                       0.
% 2.45/0.98  
% 2.45/0.98  ------ Problem properties
% 2.45/0.98  
% 2.45/0.98  clauses:                                12
% 2.45/0.98  conjectures:                            3
% 2.45/0.98  epr:                                    0
% 2.45/0.98  horn:                                   11
% 2.45/0.98  ground:                                 5
% 2.45/0.98  unary:                                  5
% 2.45/0.98  binary:                                 6
% 2.45/0.98  lits:                                   20
% 2.45/0.98  lits_eq:                                6
% 2.45/0.98  fd_pure:                                0
% 2.45/0.98  fd_pseudo:                              0
% 2.45/0.98  fd_cond:                                0
% 2.45/0.98  fd_pseudo_cond:                         0
% 2.45/0.98  ac_symbols:                             0
% 2.45/0.98  
% 2.45/0.98  ------ Propositional Solver
% 2.45/0.98  
% 2.45/0.98  prop_solver_calls:                      27
% 2.45/0.98  prop_fast_solver_calls:                 407
% 2.45/0.98  smt_solver_calls:                       0
% 2.45/0.98  smt_fast_solver_calls:                  0
% 2.45/0.98  prop_num_of_clauses:                    1226
% 2.45/0.98  prop_preprocess_simplified:             3018
% 2.45/0.98  prop_fo_subsumed:                       5
% 2.45/0.98  prop_solver_time:                       0.
% 2.45/0.98  smt_solver_time:                        0.
% 2.45/0.98  smt_fast_solver_time:                   0.
% 2.45/0.98  prop_fast_solver_time:                  0.
% 2.45/0.98  prop_unsat_core_time:                   0.
% 2.45/0.98  
% 2.45/0.98  ------ QBF
% 2.45/0.98  
% 2.45/0.98  qbf_q_res:                              0
% 2.45/0.98  qbf_num_tautologies:                    0
% 2.45/0.98  qbf_prep_cycles:                        0
% 2.45/0.98  
% 2.45/0.98  ------ BMC1
% 2.45/0.98  
% 2.45/0.98  bmc1_current_bound:                     -1
% 2.45/0.98  bmc1_last_solved_bound:                 -1
% 2.45/0.98  bmc1_unsat_core_size:                   -1
% 2.45/0.98  bmc1_unsat_core_parents_size:           -1
% 2.45/0.98  bmc1_merge_next_fun:                    0
% 2.45/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.45/0.98  
% 2.45/0.98  ------ Instantiation
% 2.45/0.98  
% 2.45/0.98  inst_num_of_clauses:                    363
% 2.45/0.98  inst_num_in_passive:                    116
% 2.45/0.98  inst_num_in_active:                     212
% 2.45/0.98  inst_num_in_unprocessed:                35
% 2.45/0.98  inst_num_of_loops:                      240
% 2.45/0.98  inst_num_of_learning_restarts:          0
% 2.45/0.98  inst_num_moves_active_passive:          23
% 2.45/0.98  inst_lit_activity:                      0
% 2.45/0.98  inst_lit_activity_moves:                0
% 2.45/0.98  inst_num_tautologies:                   0
% 2.45/0.98  inst_num_prop_implied:                  0
% 2.45/0.98  inst_num_existing_simplified:           0
% 2.45/0.98  inst_num_eq_res_simplified:             0
% 2.45/0.98  inst_num_child_elim:                    0
% 2.45/0.98  inst_num_of_dismatching_blockings:      42
% 2.45/0.98  inst_num_of_non_proper_insts:           306
% 2.45/0.98  inst_num_of_duplicates:                 0
% 2.45/0.98  inst_inst_num_from_inst_to_res:         0
% 2.45/0.98  inst_dismatching_checking_time:         0.
% 2.45/0.98  
% 2.45/0.98  ------ Resolution
% 2.45/0.98  
% 2.45/0.98  res_num_of_clauses:                     0
% 2.45/0.98  res_num_in_passive:                     0
% 2.45/0.98  res_num_in_active:                      0
% 2.45/0.98  res_num_of_loops:                       79
% 2.45/0.98  res_forward_subset_subsumed:            47
% 2.45/0.98  res_backward_subset_subsumed:           0
% 2.45/0.98  res_forward_subsumed:                   0
% 2.45/0.98  res_backward_subsumed:                  0
% 2.45/0.98  res_forward_subsumption_resolution:     0
% 2.45/0.98  res_backward_subsumption_resolution:    0
% 2.45/0.98  res_clause_to_clause_subsumption:       226
% 2.45/0.98  res_orphan_elimination:                 0
% 2.45/0.98  res_tautology_del:                      48
% 2.45/0.98  res_num_eq_res_simplified:              0
% 2.45/0.98  res_num_sel_changes:                    0
% 2.45/0.98  res_moves_from_active_to_pass:          0
% 2.45/0.98  
% 2.45/0.98  ------ Superposition
% 2.45/0.98  
% 2.45/0.98  sup_time_total:                         0.
% 2.45/0.98  sup_time_generating:                    0.
% 2.45/0.98  sup_time_sim_full:                      0.
% 2.45/0.98  sup_time_sim_immed:                     0.
% 2.45/0.98  
% 2.45/0.98  sup_num_of_clauses:                     80
% 2.45/0.98  sup_num_in_active:                      43
% 2.45/0.98  sup_num_in_passive:                     37
% 2.45/0.98  sup_num_of_loops:                       47
% 2.45/0.98  sup_fw_superposition:                   46
% 2.45/0.98  sup_bw_superposition:                   32
% 2.45/0.98  sup_immediate_simplified:               8
% 2.45/0.98  sup_given_eliminated:                   0
% 2.45/0.98  comparisons_done:                       0
% 2.45/0.98  comparisons_avoided:                    0
% 2.45/0.98  
% 2.45/0.98  ------ Simplifications
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  sim_fw_subset_subsumed:                 1
% 2.45/0.98  sim_bw_subset_subsumed:                 0
% 2.45/0.98  sim_fw_subsumed:                        0
% 2.45/0.98  sim_bw_subsumed:                        0
% 2.45/0.98  sim_fw_subsumption_res:                 1
% 2.45/0.98  sim_bw_subsumption_res:                 0
% 2.45/0.98  sim_tautology_del:                      2
% 2.45/0.98  sim_eq_tautology_del:                   0
% 2.45/0.98  sim_eq_res_simp:                        0
% 2.45/0.98  sim_fw_demodulated:                     0
% 2.45/0.98  sim_bw_demodulated:                     6
% 2.45/0.98  sim_light_normalised:                   11
% 2.45/0.98  sim_joinable_taut:                      0
% 2.45/0.98  sim_joinable_simp:                      0
% 2.45/0.98  sim_ac_normalised:                      0
% 2.45/0.98  sim_smt_subsumption:                    0
% 2.45/0.98  
%------------------------------------------------------------------------------
