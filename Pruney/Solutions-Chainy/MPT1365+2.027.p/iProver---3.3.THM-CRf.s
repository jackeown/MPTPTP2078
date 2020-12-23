%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:02 EST 2020

% Result     : Theorem 11.53s
% Output     : CNFRefutation 11.53s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 496 expanded)
%              Number of clauses        :   92 ( 148 expanded)
%              Number of leaves         :   20 ( 152 expanded)
%              Depth                    :   21
%              Number of atoms          :  532 (3212 expanded)
%              Number of equality atoms :  103 ( 136 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_compts_1(X2,X0)
                  & v2_compts_1(X1,X0)
                  & v8_pre_topc(X0) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_compts_1(X2,X0)
                    & v2_compts_1(X1,X0)
                    & v8_pre_topc(X0) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v2_compts_1(X2,X0)
          & v2_compts_1(X1,X0)
          & v8_pre_topc(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v2_compts_1(sK2,X0)
        & v2_compts_1(X1,X0)
        & v8_pre_topc(X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v2_compts_1(X2,X0)
            & v2_compts_1(sK1,X0)
            & v8_pre_topc(X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_compts_1(X2,X0)
                & v2_compts_1(X1,X0)
                & v8_pre_topc(X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_compts_1(X2,sK0)
              & v2_compts_1(X1,sK0)
              & v8_pre_topc(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33,f32,f31])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f45,f37])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_740,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1397,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X1)
    | X0 != k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_10158,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,sK2),X0)
    | ~ r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),X0)
    | k9_subset_1(u1_struct_0(sK0),X0,sK2) != k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_42633,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_10158])).

cnf(c_737,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4387,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_31136,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_4387])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_742,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_3856,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_743,c_742])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_13602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_3856,c_381])).

cnf(c_13957,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[status(thm)],[c_13602,c_737])).

cnf(c_6,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | X4 != X1
    | k1_pre_topc(X1,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_8])).

cnf(c_256,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_256,c_18])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_20948,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[status(thm)],[c_13957,c_368])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20972,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) ),
    inference(resolution,[status(thm)],[c_20948,c_16])).

cnf(c_11,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_301,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_302,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_304,plain,
    ( ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(X1,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v2_compts_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_18])).

cnf(c_305,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0) ),
    inference(renaming,[status(thm)],[c_304])).

cnf(c_21790,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(sK2))
    | ~ r1_tarski(X1,X0) ),
    inference(resolution,[status(thm)],[c_20972,c_305])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24602,plain,
    ( v2_compts_1(X0,sK0)
    | ~ v2_compts_1(sK1,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | ~ r1_tarski(X0,sK1) ),
    inference(resolution,[status(thm)],[c_21790,c_17])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1169,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1163,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1160,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(X1,sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_2348,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1163,c_1160])).

cnf(c_14,negated_conjecture,
    ( v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2506,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2348,c_25])).

cnf(c_2522,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_2506])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1157,plain,
    ( u1_struct_0(k1_pre_topc(sK0,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_1418,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1163,c_1157])).

cnf(c_1158,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_2527,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X1,u1_struct_0(k1_pre_topc(sK0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1158])).

cnf(c_4783,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_2527])).

cnf(c_5212,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v2_compts_1(X0,sK0) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2522,c_22,c_25,c_2348,c_4783])).

cnf(c_5213,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5212])).

cnf(c_5214,plain,
    ( v2_compts_1(X0,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ r1_tarski(X0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5213])).

cnf(c_25766,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | v2_compts_1(X0,sK0)
    | ~ r1_tarski(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24602,c_5214])).

cnf(c_25767,plain,
    ( v2_compts_1(X0,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ r1_tarski(X0,sK1) ),
    inference(renaming,[status(thm)],[c_25766])).

cnf(c_12,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25786,plain,
    ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
    inference(resolution,[status(thm)],[c_25767,c_12])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_140,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_141,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_140])).

cnf(c_177,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_141])).

cnf(c_1453,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_18089,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1453])).

cnf(c_747,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1804,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | X0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_10177,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
    | ~ v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | X0 != sK0
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1804])).

cnf(c_10179,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_10177])).

cnf(c_738,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1739,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(X2,X3)
    | k4_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_2482,plain,
    ( X0 != k9_subset_1(u1_struct_0(sK0),X1,sK2)
    | X0 = k4_xboole_0(X1,k4_xboole_0(X1,sK2))
    | k4_xboole_0(X1,k4_xboole_0(X1,sK2)) != k9_subset_1(u1_struct_0(sK0),X1,sK2) ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_4386,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) != k9_subset_1(u1_struct_0(sK0),X0,sK2)
    | k9_subset_1(u1_struct_0(sK0),X0,sK2) = k4_xboole_0(X0,k4_xboole_0(X0,sK2))
    | k4_xboole_0(X0,k4_xboole_0(X0,sK2)) != k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_10175,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_4386])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1964,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_327,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_328,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ v4_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_18])).

cnf(c_333,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_332])).

cnf(c_1446,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_1620,plain,
    ( v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1331,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_276,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_277,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_281,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_19,c_18])).

cnf(c_1298,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1295,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_760,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_13,negated_conjecture,
    ( v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42633,c_31136,c_25786,c_18089,c_10179,c_10175,c_1964,c_1620,c_1331,c_1298,c_1295,c_760,c_13,c_14,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.53/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.53/1.99  
% 11.53/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.53/1.99  
% 11.53/1.99  ------  iProver source info
% 11.53/1.99  
% 11.53/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.53/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.53/1.99  git: non_committed_changes: false
% 11.53/1.99  git: last_make_outside_of_git: false
% 11.53/1.99  
% 11.53/1.99  ------ 
% 11.53/1.99  ------ Parsing...
% 11.53/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.53/1.99  ------ Proving...
% 11.53/1.99  ------ Problem Properties 
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  clauses                                 16
% 11.53/1.99  conjectures                             5
% 11.53/1.99  EPR                                     2
% 11.53/1.99  Horn                                    16
% 11.53/1.99  unary                                   7
% 11.53/1.99  binary                                  5
% 11.53/1.99  lits                                    34
% 11.53/1.99  lits eq                                 4
% 11.53/1.99  fd_pure                                 0
% 11.53/1.99  fd_pseudo                               0
% 11.53/1.99  fd_cond                                 0
% 11.53/1.99  fd_pseudo_cond                          0
% 11.53/1.99  AC symbols                              0
% 11.53/1.99  
% 11.53/1.99  ------ Input Options Time Limit: Unbounded
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  ------ 
% 11.53/1.99  Current options:
% 11.53/1.99  ------ 
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  ------ Proving...
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  % SZS status Theorem for theBenchmark.p
% 11.53/1.99  
% 11.53/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.53/1.99  
% 11.53/1.99  fof(f8,axiom,(
% 11.53/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f20,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.53/1.99    inference(ennf_transformation,[],[f8])).
% 11.53/1.99  
% 11.53/1.99  fof(f43,plain,(
% 11.53/1.99    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f20])).
% 11.53/1.99  
% 11.53/1.99  fof(f13,conjecture,(
% 11.53/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f14,negated_conjecture,(
% 11.53/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 11.53/1.99    inference(negated_conjecture,[],[f13])).
% 11.53/1.99  
% 11.53/1.99  fof(f28,plain,(
% 11.53/1.99    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.53/1.99    inference(ennf_transformation,[],[f14])).
% 11.53/1.99  
% 11.53/1.99  fof(f29,plain,(
% 11.53/1.99    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.53/1.99    inference(flattening,[],[f28])).
% 11.53/1.99  
% 11.53/1.99  fof(f33,plain,(
% 11.53/1.99    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v2_compts_1(sK2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.53/1.99    introduced(choice_axiom,[])).
% 11.53/1.99  
% 11.53/1.99  fof(f32,plain,(
% 11.53/1.99    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(sK1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.53/1.99    introduced(choice_axiom,[])).
% 11.53/1.99  
% 11.53/1.99  fof(f31,plain,(
% 11.53/1.99    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.53/1.99    introduced(choice_axiom,[])).
% 11.53/1.99  
% 11.53/1.99  fof(f34,plain,(
% 11.53/1.99    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.53/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33,f32,f31])).
% 11.53/1.99  
% 11.53/1.99  fof(f49,plain,(
% 11.53/1.99    l1_pre_topc(sK0)),
% 11.53/1.99    inference(cnf_transformation,[],[f34])).
% 11.53/1.99  
% 11.53/1.99  fof(f7,axiom,(
% 11.53/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f15,plain,(
% 11.53/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 11.53/1.99    inference(pure_predicate_removal,[],[f7])).
% 11.53/1.99  
% 11.53/1.99  fof(f18,plain,(
% 11.53/1.99    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.53/1.99    inference(ennf_transformation,[],[f15])).
% 11.53/1.99  
% 11.53/1.99  fof(f19,plain,(
% 11.53/1.99    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.53/1.99    inference(flattening,[],[f18])).
% 11.53/1.99  
% 11.53/1.99  fof(f42,plain,(
% 11.53/1.99    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f19])).
% 11.53/1.99  
% 11.53/1.99  fof(f9,axiom,(
% 11.53/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f21,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.53/1.99    inference(ennf_transformation,[],[f9])).
% 11.53/1.99  
% 11.53/1.99  fof(f44,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f21])).
% 11.53/1.99  
% 11.53/1.99  fof(f51,plain,(
% 11.53/1.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.53/1.99    inference(cnf_transformation,[],[f34])).
% 11.53/1.99  
% 11.53/1.99  fof(f12,axiom,(
% 11.53/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f26,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.53/1.99    inference(ennf_transformation,[],[f12])).
% 11.53/1.99  
% 11.53/1.99  fof(f27,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.53/1.99    inference(flattening,[],[f26])).
% 11.53/1.99  
% 11.53/1.99  fof(f47,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f27])).
% 11.53/1.99  
% 11.53/1.99  fof(f48,plain,(
% 11.53/1.99    v2_pre_topc(sK0)),
% 11.53/1.99    inference(cnf_transformation,[],[f34])).
% 11.53/1.99  
% 11.53/1.99  fof(f50,plain,(
% 11.53/1.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.53/1.99    inference(cnf_transformation,[],[f34])).
% 11.53/1.99  
% 11.53/1.99  fof(f6,axiom,(
% 11.53/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f30,plain,(
% 11.53/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.53/1.99    inference(nnf_transformation,[],[f6])).
% 11.53/1.99  
% 11.53/1.99  fof(f41,plain,(
% 11.53/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f30])).
% 11.53/1.99  
% 11.53/1.99  fof(f53,plain,(
% 11.53/1.99    v2_compts_1(sK1,sK0)),
% 11.53/1.99    inference(cnf_transformation,[],[f34])).
% 11.53/1.99  
% 11.53/1.99  fof(f55,plain,(
% 11.53/1.99    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 11.53/1.99    inference(cnf_transformation,[],[f34])).
% 11.53/1.99  
% 11.53/1.99  fof(f4,axiom,(
% 11.53/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f17,plain,(
% 11.53/1.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.53/1.99    inference(ennf_transformation,[],[f4])).
% 11.53/1.99  
% 11.53/1.99  fof(f38,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f17])).
% 11.53/1.99  
% 11.53/1.99  fof(f3,axiom,(
% 11.53/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f37,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f3])).
% 11.53/1.99  
% 11.53/1.99  fof(f57,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.53/1.99    inference(definition_unfolding,[],[f38,f37])).
% 11.53/1.99  
% 11.53/1.99  fof(f2,axiom,(
% 11.53/1.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f36,plain,(
% 11.53/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f2])).
% 11.53/1.99  
% 11.53/1.99  fof(f10,axiom,(
% 11.53/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k3_xboole_0(X1,X2),X0))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f22,plain,(
% 11.53/1.99    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.53/1.99    inference(ennf_transformation,[],[f10])).
% 11.53/1.99  
% 11.53/1.99  fof(f23,plain,(
% 11.53/1.99    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.53/1.99    inference(flattening,[],[f22])).
% 11.53/1.99  
% 11.53/1.99  fof(f45,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f23])).
% 11.53/1.99  
% 11.53/1.99  fof(f59,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (v4_pre_topc(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.53/1.99    inference(definition_unfolding,[],[f45,f37])).
% 11.53/1.99  
% 11.53/1.99  fof(f40,plain,(
% 11.53/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f30])).
% 11.53/1.99  
% 11.53/1.99  fof(f11,axiom,(
% 11.53/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f24,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.53/1.99    inference(ennf_transformation,[],[f11])).
% 11.53/1.99  
% 11.53/1.99  fof(f25,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.53/1.99    inference(flattening,[],[f24])).
% 11.53/1.99  
% 11.53/1.99  fof(f46,plain,(
% 11.53/1.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f25])).
% 11.53/1.99  
% 11.53/1.99  fof(f52,plain,(
% 11.53/1.99    v8_pre_topc(sK0)),
% 11.53/1.99    inference(cnf_transformation,[],[f34])).
% 11.53/1.99  
% 11.53/1.99  fof(f54,plain,(
% 11.53/1.99    v2_compts_1(sK2,sK0)),
% 11.53/1.99    inference(cnf_transformation,[],[f34])).
% 11.53/1.99  
% 11.53/1.99  cnf(c_740,plain,
% 11.53/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.53/1.99      theory(equality) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1397,plain,
% 11.53/1.99      ( r1_tarski(X0,X1)
% 11.53/1.99      | ~ r1_tarski(k4_xboole_0(X1,X2),X1)
% 11.53/1.99      | X0 != k4_xboole_0(X1,X2) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_740]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_10158,plain,
% 11.53/1.99      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,sK2),X0)
% 11.53/1.99      | ~ r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),X0)
% 11.53/1.99      | k9_subset_1(u1_struct_0(sK0),X0,sK2) != k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_1397]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_42633,plain,
% 11.53/1.99      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 11.53/1.99      | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
% 11.53/1.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_10158]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_737,plain,( X0 = X0 ),theory(equality) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4387,plain,
% 11.53/1.99      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_737]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_31136,plain,
% 11.53/1.99      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_4387]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_743,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.53/1.99      theory(equality) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_742,plain,
% 11.53/1.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 11.53/1.99      theory(equality) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_3856,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.53/1.99      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 11.53/1.99      | X2 != X0
% 11.53/1.99      | X3 != X1 ),
% 11.53/1.99      inference(resolution,[status(thm)],[c_743,c_742]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_7,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ l1_pre_topc(X1)
% 11.53/1.99      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.53/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_18,negated_conjecture,
% 11.53/1.99      ( l1_pre_topc(sK0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_380,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | u1_struct_0(k1_pre_topc(X1,X0)) = X0
% 11.53/1.99      | sK0 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_381,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_380]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_13602,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.53/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
% 11.53/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | X2 != X0 ),
% 11.53/1.99      inference(resolution,[status(thm)],[c_3856,c_381]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_13957,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
% 11.53/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(resolution,[status(thm)],[c_13602,c_737]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_6,plain,
% 11.53/1.99      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 11.53/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.53/1.99      | ~ l1_pre_topc(X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_8,plain,
% 11.53/1.99      ( ~ m1_pre_topc(X0,X1)
% 11.53/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 11.53/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ l1_pre_topc(X1) ),
% 11.53/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_255,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 11.53/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
% 11.53/1.99      | ~ l1_pre_topc(X1)
% 11.53/1.99      | ~ l1_pre_topc(X4)
% 11.53/1.99      | X4 != X1
% 11.53/1.99      | k1_pre_topc(X1,X0) != X3 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_6,c_8]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_256,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
% 11.53/1.99      | ~ l1_pre_topc(X1) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_255]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_367,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
% 11.53/1.99      | sK0 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_256,c_18]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_368,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
% 11.53/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_367]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_20948,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.53/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(resolution,[status(thm)],[c_13957,c_368]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_16,negated_conjecture,
% 11.53/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_20972,plain,
% 11.53/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) ),
% 11.53/1.99      inference(resolution,[status(thm)],[c_20948,c_16]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_11,plain,
% 11.53/1.99      ( ~ v2_compts_1(X0,X1)
% 11.53/1.99      | v2_compts_1(X2,X1)
% 11.53/1.99      | ~ v4_pre_topc(X2,X1)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ r1_tarski(X2,X0)
% 11.53/1.99      | ~ v2_pre_topc(X1)
% 11.53/1.99      | ~ l1_pre_topc(X1) ),
% 11.53/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_19,negated_conjecture,
% 11.53/1.99      ( v2_pre_topc(sK0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_301,plain,
% 11.53/1.99      ( ~ v2_compts_1(X0,X1)
% 11.53/1.99      | v2_compts_1(X2,X1)
% 11.53/1.99      | ~ v4_pre_topc(X2,X1)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ r1_tarski(X2,X0)
% 11.53/1.99      | ~ l1_pre_topc(X1)
% 11.53/1.99      | sK0 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_302,plain,
% 11.53/1.99      ( ~ v2_compts_1(X0,sK0)
% 11.53/1.99      | v2_compts_1(X1,sK0)
% 11.53/1.99      | ~ v4_pre_topc(X1,sK0)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ r1_tarski(X1,X0)
% 11.53/1.99      | ~ l1_pre_topc(sK0) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_301]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_304,plain,
% 11.53/1.99      ( ~ r1_tarski(X1,X0)
% 11.53/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ v4_pre_topc(X1,sK0)
% 11.53/1.99      | v2_compts_1(X1,sK0)
% 11.53/1.99      | ~ v2_compts_1(X0,sK0) ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_302,c_18]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_305,plain,
% 11.53/1.99      ( ~ v2_compts_1(X0,sK0)
% 11.53/1.99      | v2_compts_1(X1,sK0)
% 11.53/1.99      | ~ v4_pre_topc(X1,sK0)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ r1_tarski(X1,X0) ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_304]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_21790,plain,
% 11.53/1.99      ( ~ v2_compts_1(X0,sK0)
% 11.53/1.99      | v2_compts_1(X1,sK0)
% 11.53/1.99      | ~ v4_pre_topc(X1,sK0)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(sK2))
% 11.53/1.99      | ~ r1_tarski(X1,X0) ),
% 11.53/1.99      inference(resolution,[status(thm)],[c_20972,c_305]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_17,negated_conjecture,
% 11.53/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_24602,plain,
% 11.53/1.99      ( v2_compts_1(X0,sK0)
% 11.53/1.99      | ~ v2_compts_1(sK1,sK0)
% 11.53/1.99      | ~ v4_pre_topc(X0,sK0)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
% 11.53/1.99      | ~ r1_tarski(X0,sK1) ),
% 11.53/1.99      inference(resolution,[status(thm)],[c_21790,c_17]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4,plain,
% 11.53/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.53/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1169,plain,
% 11.53/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.53/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1163,plain,
% 11.53/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1160,plain,
% 11.53/1.99      ( v2_compts_1(X0,sK0) != iProver_top
% 11.53/1.99      | v2_compts_1(X1,sK0) = iProver_top
% 11.53/1.99      | v4_pre_topc(X1,sK0) != iProver_top
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.53/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.53/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2348,plain,
% 11.53/1.99      ( v2_compts_1(X0,sK0) = iProver_top
% 11.53/1.99      | v2_compts_1(sK1,sK0) != iProver_top
% 11.53/1.99      | v4_pre_topc(X0,sK0) != iProver_top
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.53/1.99      | r1_tarski(X0,sK1) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_1163,c_1160]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_14,negated_conjecture,
% 11.53/1.99      ( v2_compts_1(sK1,sK0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_25,plain,
% 11.53/1.99      ( v2_compts_1(sK1,sK0) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2506,plain,
% 11.53/1.99      ( v2_compts_1(X0,sK0) = iProver_top
% 11.53/1.99      | v4_pre_topc(X0,sK0) != iProver_top
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.53/1.99      | r1_tarski(X0,sK1) != iProver_top ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_2348,c_25]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2522,plain,
% 11.53/1.99      ( v2_compts_1(X0,sK0) = iProver_top
% 11.53/1.99      | v4_pre_topc(X0,sK0) != iProver_top
% 11.53/1.99      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.53/1.99      | r1_tarski(X0,sK1) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_1169,c_2506]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_22,plain,
% 11.53/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1157,plain,
% 11.53/1.99      ( u1_struct_0(k1_pre_topc(sK0,X0)) = X0
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1418,plain,
% 11.53/1.99      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_1163,c_1157]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1158,plain,
% 11.53/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1)))) != iProver_top
% 11.53/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2527,plain,
% 11.53/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.53/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.53/1.99      | r1_tarski(X1,u1_struct_0(k1_pre_topc(sK0,X0))) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_1169,c_1158]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4783,plain,
% 11.53/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.53/1.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.53/1.99      | r1_tarski(X0,sK1) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_1418,c_2527]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_5212,plain,
% 11.53/1.99      ( v4_pre_topc(X0,sK0) != iProver_top
% 11.53/1.99      | v2_compts_1(X0,sK0) = iProver_top
% 11.53/1.99      | r1_tarski(X0,sK1) != iProver_top ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_2522,c_22,c_25,c_2348,c_4783]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_5213,plain,
% 11.53/1.99      ( v2_compts_1(X0,sK0) = iProver_top
% 11.53/1.99      | v4_pre_topc(X0,sK0) != iProver_top
% 11.53/1.99      | r1_tarski(X0,sK1) != iProver_top ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_5212]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_5214,plain,
% 11.53/1.99      ( v2_compts_1(X0,sK0)
% 11.53/1.99      | ~ v4_pre_topc(X0,sK0)
% 11.53/1.99      | ~ r1_tarski(X0,sK1) ),
% 11.53/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_5213]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_25766,plain,
% 11.53/1.99      ( ~ v4_pre_topc(X0,sK0)
% 11.53/1.99      | v2_compts_1(X0,sK0)
% 11.53/1.99      | ~ r1_tarski(X0,sK1) ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_24602,c_5214]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_25767,plain,
% 11.53/1.99      ( v2_compts_1(X0,sK0)
% 11.53/1.99      | ~ v4_pre_topc(X0,sK0)
% 11.53/1.99      | ~ r1_tarski(X0,sK1) ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_25766]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_12,negated_conjecture,
% 11.53/1.99      ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_25786,plain,
% 11.53/1.99      ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 11.53/1.99      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
% 11.53/1.99      inference(resolution,[status(thm)],[c_25767,c_12]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.53/1.99      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_140,plain,
% 11.53/1.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.53/1.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_141,plain,
% 11.53/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_140]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_177,plain,
% 11.53/1.99      ( ~ r1_tarski(X0,X1)
% 11.53/1.99      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 11.53/1.99      inference(bin_hyper_res,[status(thm)],[c_2,c_141]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1453,plain,
% 11.53/1.99      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 11.53/1.99      | k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_177]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_18089,plain,
% 11.53/1.99      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 11.53/1.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_1453]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_747,plain,
% 11.53/1.99      ( ~ v4_pre_topc(X0,X1) | v4_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.53/1.99      theory(equality) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1804,plain,
% 11.53/1.99      ( v4_pre_topc(X0,X1)
% 11.53/1.99      | ~ v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
% 11.53/1.99      | X0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 11.53/1.99      | X1 != sK0 ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_747]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_10177,plain,
% 11.53/1.99      ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
% 11.53/1.99      | ~ v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
% 11.53/1.99      | X0 != sK0
% 11.53/1.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_1804]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_10179,plain,
% 11.53/1.99      ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 11.53/1.99      | ~ v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
% 11.53/1.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 11.53/1.99      | sK0 != sK0 ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_10177]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_738,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1739,plain,
% 11.53/1.99      ( X0 != X1 | X0 = k4_xboole_0(X2,X3) | k4_xboole_0(X2,X3) != X1 ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_738]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2482,plain,
% 11.53/1.99      ( X0 != k9_subset_1(u1_struct_0(sK0),X1,sK2)
% 11.53/1.99      | X0 = k4_xboole_0(X1,k4_xboole_0(X1,sK2))
% 11.53/1.99      | k4_xboole_0(X1,k4_xboole_0(X1,sK2)) != k9_subset_1(u1_struct_0(sK0),X1,sK2) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_1739]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4386,plain,
% 11.53/1.99      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) != k9_subset_1(u1_struct_0(sK0),X0,sK2)
% 11.53/1.99      | k9_subset_1(u1_struct_0(sK0),X0,sK2) = k4_xboole_0(X0,k4_xboole_0(X0,sK2))
% 11.53/1.99      | k4_xboole_0(X0,k4_xboole_0(X0,sK2)) != k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_2482]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_10175,plain,
% 11.53/1.99      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
% 11.53/1.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 11.53/1.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_4386]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1,plain,
% 11.53/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f36]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1964,plain,
% 11.53/1.99      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_9,plain,
% 11.53/1.99      ( ~ v4_pre_topc(X0,X1)
% 11.53/1.99      | ~ v4_pre_topc(X2,X1)
% 11.53/1.99      | v4_pre_topc(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1)
% 11.53/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ v2_pre_topc(X1)
% 11.53/1.99      | ~ l1_pre_topc(X1) ),
% 11.53/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_327,plain,
% 11.53/1.99      ( ~ v4_pre_topc(X0,X1)
% 11.53/1.99      | ~ v4_pre_topc(X2,X1)
% 11.53/1.99      | v4_pre_topc(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ l1_pre_topc(X1)
% 11.53/1.99      | sK0 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_328,plain,
% 11.53/1.99      ( ~ v4_pre_topc(X0,sK0)
% 11.53/1.99      | ~ v4_pre_topc(X1,sK0)
% 11.53/1.99      | v4_pre_topc(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sK0)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ l1_pre_topc(sK0) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_327]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_332,plain,
% 11.53/1.99      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | v4_pre_topc(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sK0)
% 11.53/1.99      | ~ v4_pre_topc(X1,sK0)
% 11.53/1.99      | ~ v4_pre_topc(X0,sK0) ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_328,c_18]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_333,plain,
% 11.53/1.99      ( ~ v4_pre_topc(X0,sK0)
% 11.53/1.99      | ~ v4_pre_topc(X1,sK0)
% 11.53/1.99      | v4_pre_topc(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sK0)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_332]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1446,plain,
% 11.53/1.99      ( ~ v4_pre_topc(X0,sK0)
% 11.53/1.99      | v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),sK0)
% 11.53/1.99      | ~ v4_pre_topc(sK1,sK0)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_333]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1620,plain,
% 11.53/1.99      ( v4_pre_topc(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
% 11.53/1.99      | ~ v4_pre_topc(sK2,sK0)
% 11.53/1.99      | ~ v4_pre_topc(sK1,sK0)
% 11.53/1.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_1446]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_5,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.53/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1331,plain,
% 11.53/1.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_10,plain,
% 11.53/1.99      ( ~ v2_compts_1(X0,X1)
% 11.53/1.99      | v4_pre_topc(X0,X1)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ v8_pre_topc(X1)
% 11.53/1.99      | ~ v2_pre_topc(X1)
% 11.53/1.99      | ~ l1_pre_topc(X1) ),
% 11.53/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15,negated_conjecture,
% 11.53/1.99      ( v8_pre_topc(sK0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_276,plain,
% 11.53/1.99      ( ~ v2_compts_1(X0,X1)
% 11.53/1.99      | v4_pre_topc(X0,X1)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ v2_pre_topc(X1)
% 11.53/1.99      | ~ l1_pre_topc(X1)
% 11.53/1.99      | sK0 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_277,plain,
% 11.53/1.99      ( ~ v2_compts_1(X0,sK0)
% 11.53/1.99      | v4_pre_topc(X0,sK0)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ v2_pre_topc(sK0)
% 11.53/1.99      | ~ l1_pre_topc(sK0) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_276]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_281,plain,
% 11.53/1.99      ( ~ v2_compts_1(X0,sK0)
% 11.53/1.99      | v4_pre_topc(X0,sK0)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_277,c_19,c_18]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1298,plain,
% 11.53/1.99      ( ~ v2_compts_1(sK1,sK0)
% 11.53/1.99      | v4_pre_topc(sK1,sK0)
% 11.53/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_281]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1295,plain,
% 11.53/1.99      ( ~ v2_compts_1(sK2,sK0)
% 11.53/1.99      | v4_pre_topc(sK2,sK0)
% 11.53/1.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_281]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_760,plain,
% 11.53/1.99      ( sK0 = sK0 ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_737]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_13,negated_conjecture,
% 11.53/1.99      ( v2_compts_1(sK2,sK0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(contradiction,plain,
% 11.53/1.99      ( $false ),
% 11.53/1.99      inference(minisat,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_42633,c_31136,c_25786,c_18089,c_10179,c_10175,c_1964,
% 11.53/1.99                 c_1620,c_1331,c_1298,c_1295,c_760,c_13,c_14,c_16,c_17]) ).
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.53/1.99  
% 11.53/1.99  ------                               Statistics
% 11.53/1.99  
% 11.53/1.99  ------ Selected
% 11.53/1.99  
% 11.53/1.99  total_time:                             1.311
% 11.53/1.99  
%------------------------------------------------------------------------------
